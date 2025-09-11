module Verifier {
  import opened Std.Wrappers
  import opened Basics
  import opened Ast
  import opened SolverExpr
  import AstValid
  import I = Incarnations
  import RSolvers
  import StaticConsistency
  import AssignmentTargets
  import SpecConversions
  import BC = BlockContinuations
  import CLI = CommandLineOptions

  export
    provides Verify
    provides Ast, AstValid, CLI, StaticConsistency

  method Verify(b3: Ast.Program, cli: CLI.CliResult)
    requires AstValid.Program(b3)
  {
    // Create STypeDecl and SConstant declarations for the B3 types, taggers, and functions

    var typeMap := map[];
    for i := 0 to |b3.types| {
      var typ := b3.types[i];
      var t := new STypeDecl(typ.Name);
      typeMap := typeMap[typ := t];
    }

    var functionMap := map[];
    for i := 0 to |b3.functions| {
      var func := b3.functions[i];
      var inputTypes := SeqMap(func.Parameters, (parameter: FParameter) => I.DeclMappings.Type2STypeWithMap(parameter.typ, typeMap));
      var f := new SConstant.Function(func.Name, inputTypes, I.DeclMappings.Type2STypeWithMap(func.ResultType, typeMap));
      functionMap := functionMap[func := f];
    }

    var declMap := I.DeclMappings(typeMap, functionMap);

    // Add undifferentiated axioms to context (i.e., those axioms that don't explain specific functions).
    // For the other axioms (i.e., those that explain functions), do the .REval and add them to the axiomMap
    var context := RSolvers.CreateEmptyContext();
    var axiomIncarnations := I.Incarnations.Empty(declMap);
    var axiomMap := map[];
    for i := 0 to |b3.axioms| {
      var axiom := b3.axioms[i];
      assert axiom.WellFormed();
      var cond := axiomIncarnations.REval(axiom.Expr);
      if axiom.Explains == [] {
        context := RSolvers.Extend(context, cond);
      } else {
        axiomMap := axiomMap[axiom := cond];
      }
    }

    // Verify each procedure

    for i := 0 to |b3.procedures| {
      var proc := b3.procedures[i];
      print "Verifying ", proc.Name, " ...\n";
      VerifyProcedure(proc, context, declMap, axiomMap, cli);
    }
  }

  method VerifyProcedure(proc: Ast.Procedure, context_in: RSolvers.RContext, declMap: I.DeclMappings, axiomMap: map<Axiom, RSolvers.RExpr>, cli: CLI.CliResult)
    requires AstValid.Procedure(proc)
  {
    var smtEngine := RSolvers.CreateEngine(axiomMap, cli);
    var preIncarnations, bodyIncarnations, postIncarnations := CreateProcIncarnations(proc.Parameters, declMap);

    {
      var context := context_in;
      context := VetSpecification(proc.Pre, preIncarnations, context, smtEngine);
      var _ := VetSpecification(proc.Post, postIncarnations, context, smtEngine);
    }

    if proc.Body.Some? {
      var body := proc.Body.value;
      var context := context_in;

      var preLearning := SpecConversions.ToLearn(proc.Pre);
      context := ProcessPredicateStmts(preLearning, postIncarnations, context, smtEngine);

      var postCheck := SpecConversions.ToCheck(proc.Post);
      Process([body] + postCheck, bodyIncarnations, context, BC.Empty(), smtEngine);
    }
  }

  method CreateProcIncarnations(parameters: seq<Parameter>, declMap: I.DeclMappings)
      returns (preIncarnations: I.Incarnations, bodyIncarnations: I.Incarnations, postIncarnations: I.Incarnations)
    requires forall i :: 0 <= i < |parameters| ==> parameters[i].WellFormed()
  {
    preIncarnations, bodyIncarnations, postIncarnations := I.Incarnations.Empty(declMap), I.Incarnations.Empty(declMap), I.Incarnations.Empty(declMap);
    for i := 0 to |parameters| {
      var parameter := parameters[i];
      match parameter.mode
      case In =>
        var v := new SConstant(parameter.name, declMap.Type2SType(parameter.typ));
        preIncarnations := preIncarnations.Set(parameter, v);
        bodyIncarnations := bodyIncarnations.Set(parameter, v);
        postIncarnations := postIncarnations.Set(parameter, v);
      case InOut =>
        var vOld := new SConstant(parameter.name + "%old", declMap.Type2SType(parameter.typ));
        preIncarnations := preIncarnations.Set(parameter, vOld);
        bodyIncarnations := bodyIncarnations.Set(parameter.oldInOut.value, vOld);
        bodyIncarnations := bodyIncarnations.Set(parameter, vOld);
        postIncarnations := postIncarnations.Set(parameter.oldInOut.value, vOld);
        var v := new SConstant(parameter.name, declMap.Type2SType(parameter.typ));
        postIncarnations := postIncarnations.Set(parameter, v);
      case out =>
        var v := new SConstant(parameter.name, declMap.Type2SType(parameter.typ));
        bodyIncarnations := bodyIncarnations.Set(parameter, v);
        postIncarnations := postIncarnations.Set(parameter, v);
    }
  }

  method VetSpecification(spec: seq<AExpr>,
                          incarnations: I.Incarnations, context_in: RSolvers.RContext, smtEngine: RSolvers.REngine,
                          ghost parent: Stmt := Loop(spec, Block([])))
      returns (context: RSolvers.RContext)
    requires AstValid.AExprSeq(spec)
    requires forall aexpr <- spec :: aexpr < parent
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
    decreases BC.AExprsMeasure(spec, parent)
  {
    context := context_in;
    for i := 0 to |spec|
      invariant smtEngine.Valid()
    {
      assert spec[i] in spec;
      match spec[i]
      case AExpr(cond) =>
        var rCond := incarnations.REval(cond);
        context := RSolvers.Extend(context, rCond);
      case AAssertion(s) =>
        assert BC.AExprsMeasure(spec, parent) > BC.StmtSeqMeasure([s]) + BC.ContinuationsMeasure(BC.Empty()) by {
          BC.AboutAExprsMeasure(s, spec, parent);
          BC.AboutStmtSeqMeasureSingleton(s);
          BC.ContinuationsMeasureEmpty();
        }
        Process([s], incarnations, context, BC.Empty(), smtEngine);
        var L := SpecConversions.Learn(s);
        var rL := incarnations.REval(L);
        context := RSolvers.Extend(context, rL);
    }
  }

  method Process(stmts: seq<Stmt>, incarnations_in: I.Incarnations, context_in: RSolvers.RContext, B: BC.T, smtEngine: RSolvers.REngine)
    requires AstValid.StmtSeq(stmts) && BC.Valid(B) && smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
    decreases BC.StmtSeqMeasure(stmts) + BC.ContinuationsMeasure(B)
  {
    if stmts == [] {
      return;
    }

    var incarnations, context := incarnations_in, context_in;
    var stmt, cont := stmts[0], stmts[1..];
    assert AstValid.Stmt(stmt);
    BC.StmtMeasureSplit(stmts);

    if stmt.IsPredicateStmt() {
      context := ProcessPredicateStmt(stmt, incarnations, context, smtEngine);
      Process(cont, incarnations, context, B, smtEngine);
      return;
    }

    match stmt
    case VarDecl(v, init, body) =>
      var sv;
      incarnations, sv := incarnations.Update(v);
      if init.Some? {
        var sRhs := incarnations.REval(init.value);
        context := RSolvers.ExtendWithEquality(context, sv, sRhs);
      }
      BC.StmtMeasurePrepend(body, cont);
      Process([body] + cont, incarnations, context, B, smtEngine);
    case Assign(lhs, rhs) =>
      var sRhs := incarnations.REval(rhs);
      var sLhs;
      incarnations, sLhs := incarnations.Update(lhs);
      context := RSolvers.ExtendWithEquality(context, sLhs, sRhs);
      Process(cont, incarnations, context, B, smtEngine);
    case Block(stmts) =>
      BC.AboutStmtSeqMeasureConcat(stmts, cont);
      Process(stmts + cont, incarnations, context, B, smtEngine);
    case Call(_, _) =>
      incarnations, context := ProcessCall(stmt, incarnations, context, smtEngine);
      Process(cont, incarnations, context, B, smtEngine);
    case AForall(v, body) =>
      var bodyIncarnations, _ := incarnations.Update(v);
      BC.AboutStmtSeqMeasureSingleton(body);
      Process([body], bodyIncarnations, context, B, smtEngine);
      assert !StaticConsistency.ContainsNonAssertions(stmt);
      var L := SpecConversions.Learn(stmt);
      var rL := incarnations.REval(L);
      context := RSolvers.Extend(context, rL);
      Process(cont, incarnations, context, B, smtEngine);
    case Choose(branches) =>
      for i := 0 to |branches|
        invariant smtEngine.Valid()
      {
        BC.StmtSeqElement(branches, i);
        BC.StmtMeasurePrepend(branches[i], cont);
        Process([branches[i]] + cont, incarnations, context, B, smtEngine);
      }
    case Loop(_, _) =>
      // `cont` is ignored, since a `loop` never has any normal exit
      ProcessLoop(stmt, incarnations, context, B, smtEngine);
    case LabeledStmt(lbl, body) =>
      var B' := BC.Add(B, lbl, incarnations.Variables(), cont);
      BC.AboutContinuationsMeasureAdd(B, lbl, incarnations.Variables(), cont);
      BC.StmtPairMeasure(body, Exit(lbl));
      Process([body, Exit(lbl)], incarnations, context, B', smtEngine);
    case Exit(lbl) =>
      expect lbl in B, lbl.Name; // TODO
      var c := BC.Get(B, lbl);
      var variablesInScope, cont := c.variablesInScope, c.continuation;
      var incarnations' := incarnations.DomainRestrict(variablesInScope);
      var B0 := BC.Remove(B, lbl);
      assert B == B0[lbl := BC.Continuation(variablesInScope, cont)];
      assert B == BC.Add(B0, lbl, variablesInScope, cont);
      assert BC.ContinuationsMeasure(B) >= BC.StmtSeqMeasure(cont) + BC.ContinuationsMeasure(B0) by {
        BC.AboutContinuationsMeasure(B0, lbl, variablesInScope, cont);
      }
      Process(cont, incarnations', context, B0, smtEngine);
    case Probe(e) =>
      var rExpr := incarnations.REval(e);
      context := RSolvers.Record(context, rExpr, incarnations.Type2SType(e.ExprType()));
      Process(cont, incarnations, context, B, smtEngine);
  }

  method ProcessPredicateStmt(stmt: Stmt, incarnations: I.Incarnations, context_in: RSolvers.RContext, smtEngine: RSolvers.REngine)
      returns (context: RSolvers.RContext)
    requires AstValid.Stmt(stmt) && stmt.IsPredicateStmt()
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
  {
    context := context_in;
    match stmt
    case Check(cond) =>
      var rCond := incarnations.REval(cond);
      ProveAndReport(context, rCond, "check", cond, smtEngine);
    case Assume(cond) =>
      var rCond := incarnations.REval(cond);
      context := RSolvers.Extend(context, rCond);
    case Assert(cond) =>
      var rCond := incarnations.REval(cond);
      ProveAndReport(context, rCond, "assert", cond, smtEngine);
      context := RSolvers.Extend(context, rCond);
  }

  method ProcessCall(stmt: Stmt, incarnations_in: I.Incarnations, context_in: RSolvers.RContext, smtEngine: RSolvers.REngine)
      returns (incarnations: I.Incarnations, context: RSolvers.RContext)
    requires AstValid.Stmt(stmt) && stmt.Call?
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
  {
    var Call(proc, args) := stmt;
    assume {:axiom} AstValid.ProcedureHeader(proc); // TODO
    incarnations, context := incarnations_in, context_in;

    // While evolving "incarnations", create two incarnation sub-maps:
    //   * preIncarnations, whose domain is proc's in- and inout-parameters
    //   * postIncarnations, whose domain is proc's in-parameters, old and new inout-parameters, and out-parameters.
    // Both of these sub-maps will take proc's in-parameters to fresh names in "incarnations".
    // "preIncarnations" will take the inout-parameters to the (same incarnations as the) actual inout-parameters (in the pre-state of the call),
    // and "postIncarnations" will take the old inout-parameters to those same incarnations.
    // "postIncarnations" will take the inout- and out-parameters to fresh names for the actual inout- and out-parameters.
    // Meanwhile, the fresh names used for the in-parameters must not be used again in "incarnations", and the final
    // incarnations for the actual inout- and out-parameters will be those used in "postIncarnations".
    //
    // Example: Suppose "proc" is declared with formal parameters
    //     procedure proc(x, inout y, out z)
    // and "args" uses the actual parameters
    //     call proc(e, inout b, out c)
    // where "e" is an expression and "b" and "c" are variables. Suppose furthermore that "incarnations" includes the
    // following mappings:
    //     b := "b14"
    //     c := "c8"
    //     x := "x10"
    //     y := "y29"
    //     z := "z2"
    //     k := "k19"
    // "preIncarnations" will then be computed to be:
    //     x := "x11"
    //     y := "b14"
    // "postIncarnations" will be:
    //     x := "x11"
    //     y.old := "b14"
    //     y := "b15"
    //     z := "c9"
    // The returned value of "incarnations" will be:
    //     b := "b15"
    //     c := "c9"
    //     x := "x10"  // but the subsequent incarnation for "x" will be "x12", since "x11" has already been used
    //     y := "y29"
    //     z := "z2"
    //     k := "k19"
    var preMap: map<Variable, SConstant>, postMap: map<Variable, SConstant> := map[], map[];
    for i := 0 to |args|
      invariant smtEngine.Valid()
    {
      assert args[i] in args;
      var formal := proc.Parameters[i];
      match args[i]
      case InArgument(e) =>
        var freshIncarnation;
        incarnations, freshIncarnation := incarnations.Reserve(formal);
        preMap := preMap[formal := freshIncarnation];
        postMap := postMap[formal := freshIncarnation];

        var actual := incarnations_in.REval(e);
        context := RSolvers.ExtendWithEquality(context, preMap[formal], actual);

      case OutgoingArgument(isInOut, v) =>
        if isInOut {
          assert formal.oldInOut.Some?;
          var incomingIncarnation := incarnations_in.Get(v);
          preMap := preMap[formal := incomingIncarnation];
          postMap := postMap[formal.oldInOut.value := incomingIncarnation];
        }
        var freshIncarnation;
        incarnations, freshIncarnation := incarnations.Update(formal);
        postMap := postMap[formal := freshIncarnation];
    }
    var preIncarnations := incarnations.CreateSubMap(preMap);
    var postIncarnations := incarnations.CreateSubMap(postMap);

    // check preconditions, then drop them
    assert AstValid.AExprSeq(proc.Pre); // this should come from well-formedness of program/context
    var preChecks := SpecConversions.ToCheck(proc.Pre);
    var _ := ProcessPredicateStmts(preChecks, preIncarnations, context, smtEngine);

    // learn postconditions
    var postLearning := SpecConversions.ToLearn(proc.Post);
    context := ProcessPredicateStmts(postLearning, postIncarnations, context, smtEngine);
  }

  method ProcessPredicateStmts(stmts: seq<Stmt>, incarnations: I.Incarnations, context_in: RSolvers.RContext, smtEngine: RSolvers.REngine) returns (context: RSolvers.RContext)
    requires AstValid.StmtSeq(stmts) && SpecConversions.JustPredicateStmts(stmts)
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
  {
    context := context_in;

    for i := 0 to |stmts|
      invariant smtEngine.Valid()
    {
      context := ProcessPredicateStmt(stmts[i], incarnations, context, smtEngine);
    }
  }

  method ProcessLoop(stmt: Stmt, incarnations_in: I.Incarnations, context_in: RSolvers.RContext, B: BC.T, smtEngine: RSolvers.REngine)
    requires AstValid.Stmt(stmt) && stmt.Loop?
    requires BC.Valid(B) && smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
    decreases BC.StmtMeasure(stmt) + BC.ContinuationsMeasure(B), 0
  {
    var Loop(invariants, body) := stmt;
    var incarnations, context := incarnations_in, context_in;

    // check the invariant on entry, then drop it
    var initChecks := SpecConversions.ToCheck(invariants);
    var _ := ProcessPredicateStmts(initChecks, incarnations, context, smtEngine);

    // Havoc the assignment targets of the loop body
    var assignmentTargets := AssignmentTargets.Compute(body);
    while assignmentTargets != {}
      invariant smtEngine.Valid()
    {
      var v :| v in assignmentTargets;
      assignmentTargets := assignmentTargets - {v};
      var sv;
      incarnations, sv := incarnations.Update(v);
    }

    var _ := VetSpecification(invariants, incarnations, context, smtEngine, stmt);

    var assumeInvariants := SpecConversions.ToLearn(invariants);
    var maintainanceChecks := SpecConversions.ToCheck(invariants);
    // Process body
    assert BC.StmtMeasure(stmt) > BC.StmtSeqMeasure(assumeInvariants + [body] + maintainanceChecks) by {
      calc {
        BC.StmtMeasure(stmt);
        1 + BC.AExprsMeasure(invariants, stmt) + 4 * |invariants| + BC.StmtMeasure(body);
      >=
        1 + 4 * |invariants| + BC.StmtMeasure(body);
      >  { BC.JustPredicateStmtsMeasure(assumeInvariants); BC.JustPredicateStmtsMeasure(maintainanceChecks); }
        BC.StmtSeqMeasure(assumeInvariants) + BC.StmtMeasure(body) + BC.StmtSeqMeasure(maintainanceChecks);
        { BC.AboutStmtSeqMeasureSingleton(body); }
        BC.StmtSeqMeasure(assumeInvariants) + BC.StmtSeqMeasure([body]) + BC.StmtSeqMeasure(maintainanceChecks);
        { BC.AboutStmtSeqMeasureConcat(assumeInvariants, [body]); }
        BC.StmtSeqMeasure(assumeInvariants + [body]) + BC.StmtSeqMeasure(maintainanceChecks);
        { BC.AboutStmtSeqMeasureConcat(assumeInvariants + [body], maintainanceChecks); }
        BC.StmtSeqMeasure(assumeInvariants + [body] + maintainanceChecks);
      }
    }
    Process(assumeInvariants + [body] + maintainanceChecks, incarnations, context, B, smtEngine);
  }

  // `errorReportingInfo` is currently an expression that, together with `errorText`, gets printed
  // if `context ==> expr` cannot be proved by `smtEngine`.
  // TODO: This should be improved to instead use source locations.
  method ProveAndReport(context: RSolvers.RContext, expr: RSolvers.RExpr, errorText: string, errorReportingInfo: Expr, smtEngine: RSolvers.REngine)
    requires smtEngine.Valid()
    modifies smtEngine.Repr
    ensures smtEngine.Valid()
  {
    var result := smtEngine.Prove(context, expr);
    match result
    case Proved =>
    case Unproved(reason) =>
      print "Error: Failed to prove ", errorText, " ", errorReportingInfo.ToString(), "\n";
      print "Reason: ", reason, "\n";
  }
}