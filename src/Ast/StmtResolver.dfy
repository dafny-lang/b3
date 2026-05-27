module StmtResolver {
  import opened Std.Wrappers
  import Raw = RawAst
  import opened Ast
  import opened TypeResolver
  import opened ExprResolver
  import Printer

  export
    reveals ProcResolverState, ProcResolverState.Valid, LocalResolverState
    provides ResolveStmt, ResolveAExprs, LocalResolverState.LabelSet
    provides Raw, Ast, Wrappers, ExprResolver

  datatype ProcResolverState = ProcResolverState(ers: ExprResolverState, maybeProcMap: Option<map<string, Procedure>>)
  {
    ghost predicate Valid() {
      && ers.Valid()
      && match maybeProcMap {
        case None => true
        case Some(procMap) =>
          && (forall procname <- procMap :: exists proc <- ers.b3.procedures :: proc.name == procname)
          && (forall rawProc <- ers.b3.procedures ::
                && rawProc.name in procMap
                && var proc := procMap[rawProc.name];
                && |rawProc.parameters| == |proc.Parameters|
                && (forall i :: 0 <= i < |rawProc.parameters| ==> rawProc.parameters[i].mode == proc.Parameters[i].mode)
            )
      }
    }
  }

  datatype LocalResolverState = LocalResolverState(
    varMap: map<string, Variable>,
    labelMap: map<string, Label>,
    loopLabel: Option<Label>,
    returnLabel: Option<Label>)
  {
    function AddVariable(name: string, v: Variable): LocalResolverState
      ensures AddVariable(name, v).varMap.Keys == varMap.Keys + {name}
    {
      this.(varMap := varMap[name := v])
    }

    function FindLabel(name: string): Result<Label, string> {
      if name in labelMap then
        Success(labelMap[name])
      else
        Failure("undeclared exit label: " + name)
    }

    function LabelSet(): set<string>
      ensures labelMap == map[] ==> LabelSet() == {}
    {
      labelMap.Keys
    }

    function AddLabel(name: string, lbl: Label): LocalResolverState
      ensures AddLabel(name, lbl).labelMap.Keys == labelMap.Keys + {name}
    {
      this.(labelMap := labelMap[name := lbl])
    }

    method GenerateLoopLabel() returns (lbl: Label, ls: LocalResolverState)
      ensures ls.varMap.Keys == varMap.Keys
      ensures ls.LabelSet() == LabelSet()
      ensures ls.loopLabel.Some?
    {
      lbl := new Label("loop");
      ls := this.(loopLabel := Some(lbl));
    }
  }

  method ResolveStmt(stmt: Raw.Stmt, prs: ProcResolverState, ls: LocalResolverState) returns (result: Result<Stmt, string>)
    requires prs.Valid()
    ensures result.Success? ==> stmt.WellFormed(prs.ers.b3, prs.ers.generatedTypes, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
    ensures result.Success? ==> result.value.WellFormed()
  {
    var r: Stmt;
    match stmt {
      case VarDecl(variable, init, body) =>
        if !Raw.LegalVariableName(variable.name) {
          return Failure("illegal variable name: " + variable.name);
        }
        var i;
        if init == None {
          i := None;
        } else {
          var e :- ResolveExpr(init.value, prs.ers, ls.varMap);
          i := Some(e);
        }
        var typ;
        match variable.optionalType {
          case None =>
            if i == None {
              return Failure("variable declaration must give a type or an initializing expression (or both)");
            }
            typ := i.value.ExprType();
          case Some(typeName) =>
            typ :- ResolveType(typeName, prs.ers.typeMap);
        }
        var v := new LocalVariable(variable.name, variable.isMutable, typ);
        var ls' := ls.AddVariable(variable.name, v);
        assert ls'.varMap.Keys == ls.varMap.Keys + {v.name};
        var maybeAutoInv :- ResolveMaybeExpr(variable.optionalAutoInv, prs.ers, ls'.varMap);
        v.maybeAutoInv := maybeAutoInv;
        var b :- ResolveStmt(body, prs, ls');
        r := VarDecl(v, i, b);

      case Assign(lhs, rhs) =>
        if lhs !in ls.varMap {
          return Failure("undeclared variable: " + lhs);
        }
        var left := ls.varMap[lhs];
        var right :- ResolveExpr(rhs, prs.ers, ls.varMap);
        r := Assign(left, right);

      case Reinit(vars) =>
        var resolvedVars := [];
        for n := 0 to |vars|
          invariant forall name <- vars[..n] :: name in ls.varMap
          invariant forall i, j :: 0 <= i < j < |resolvedVars| ==> resolvedVars[i] != resolvedVars[j]
        {
          var name := vars[n];
          if name !in ls.varMap {
            return Failure("undeclared variable: " + name);
          }
          var v := ls.varMap[name];
          if v !in resolvedVars {
            resolvedVars := resolvedVars + [v];
          }
        }
        r := Reinit(resolvedVars);

      case Block(stmts) =>
        var ss := [];
        for n := 0 to |stmts|
          invariant forall stmt <- stmts[..n] :: stmt.WellFormed(prs.ers.b3, prs.ers.generatedTypes, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
          invariant forall stmt: Stmt <- ss :: stmt.WellFormed()
        {
          var s :- ResolveStmt(stmts[n], prs, ls);
          ss := ss + [s];
        }
        r := Block(ss);

      case Call(_, _) =>
        r :- ResolveCallStmt(stmt, prs, ls);

      case Check(cond) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        var location := new Location("check " + c.ToString());
        r := Check(c, location);

      case Assume(cond) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        r := Assume(c);

      case Reach(cond) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        var location := new Location("reach " + c.ToString());
        r := Reach(c, location);

      case Assert(cond) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        var location := new Location("assert " + c.ToString());
        r := Assert(c, location);

      case AForall(name, typ, body) =>
        if !Raw.LegalVariableName(name) {
          return Failure("illegal variable name: " + name);
        }
        var t :- ResolveType(typ, prs.ers.typeMap);
        var v := new LocalVariable(name, false, t);
        var b :- ResolveStmt(body, prs, ls.AddVariable(name, v));
        r := AForall(v, b);

      case Choose(branches) =>
        if |branches| == 0 {
          return Failure("a choose statement must have at least 1 branch");
        }
        var rbranches := [];
        for n := 0 to |branches|
          invariant forall branch <- branches[..n] ::
            branch.WellFormed(prs.ers.b3, prs.ers.generatedTypes, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
          invariant forall branch: Stmt <- rbranches :: branch.WellFormed()
        {
          var rbranch :- ResolveStmt(branches[n], prs, ls);
          rbranches := rbranches + [rbranch];
        }
        r := Choose(rbranches);

      case If(cond, thn, els) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        var th :- ResolveStmt(thn, prs, ls);
        var el :- ResolveStmt(els, prs, ls);
        var branch0 := PrependAssumption(c, th);
        var branch1 := PrependAssumption(Expr.CreateNegation(c), el);
        r := Choose([branch0, branch1]);

      case IfCase(cases) =>
        if |cases| == 0 {
          return Failure("an if-case statement must have at least 1 case");
        }
        var branches := [];
        for n := 0 to |cases|
          invariant forall cs <- cases[..n] ::
            && cs.cond.WellFormed(prs.ers.b3, ls.varMap.Keys)
            && cs.body.WellFormed(prs.ers.b3, prs.ers.generatedTypes, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
          invariant forall branch: Stmt <- branches :: branch.WellFormed()
        {
          var cond :- ResolveExpr(cases[n].cond, prs.ers, ls.varMap);
          var body :- ResolveStmt(cases[n].body, prs, ls);
          branches := branches + [PrependAssumption(cond, body)];
        }
        r := Choose(branches);

      case Loop(invariants, body) =>
        var invs :- ResolveAExprs(invariants, prs.ers, ls);
        var loopLabel, ls' := ls.GenerateLoopLabel();
        var b :- ResolveStmt(body, prs, ls');
        r := LabeledStmt(loopLabel, Loop(invs, b));
        assert stmt.WellFormed(prs.ers.b3, prs.ers.generatedTypes, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?) by {
          assert forall ae <- invariants :: ae.WellFormed(prs.ers.b3, prs.ers.generatedTypes, ls.varMap.Keys);
          assert ls.varMap.Keys == ls'.varMap.Keys;
          assert ls.LabelSet() == ls'.LabelSet();
          assert ls'.loopLabel.Some?;
          assert body.WellFormed(prs.ers.b3, prs.ers.generatedTypes, ls'.varMap.Keys, ls'.LabelSet(), ls'.loopLabel.Some?);
        }

      case LabeledStmt(lbl, body) =>
        if lbl in ls.labelMap {
          return Failure("shadowed label name: " + lbl);
        }
        var l := new Label(lbl);
        var b :- ResolveStmt(body, prs, ls.AddLabel(lbl, l));
        r := LabeledStmt(l, b);

      case Exit(maybeLabel) =>
        match maybeLabel {
          case None =>
            if ls.loopLabel == None {
              return Failure("an 'exit' statement outside a loop requires a label");
            }
            r := Exit(ls.loopLabel.value);
          case Some(name) =>
            var lbl :- ls.FindLabel(name);
            r := Exit(lbl);
        }

      case Return =>
        if ls.returnLabel == None {
          return Failure("a 'return' statement cannot be used here");
        }
        r := Exit(ls.returnLabel.value);

      case Probe(expr) =>
        var e :- ResolveExpr(expr, prs.ers, ls.varMap);
        r := Probe(e);
    }
    return Success(r);
  }

  method ResolveCallStmt(stmt: Raw.Stmt, prs: ProcResolverState, ls: LocalResolverState) returns (result: Result<Stmt, string>)
    requires stmt.Call? && prs.Valid()
    ensures result.Success? ==> stmt.WellFormed(prs.ers.b3, prs.ers.generatedTypes, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
    ensures result.Success? ==> result.value.WellFormed()
  {
    var Call(name, args) := stmt;

    var proc;
    match prs.maybeProcMap {
      case None =>
        return Failure("procedure calls are not allowed in this context: " + name);
      case Some(procMap) =>
        if name !in procMap {
          return Failure("call to undeclared procedure: " + name);
        }
        proc := procMap[name];
    }

    var rawProc :| rawProc in prs.ers.b3.procedures && rawProc.name == name;
    assert |rawProc.parameters| == |proc.Parameters|;

    if |args| != |proc.Parameters| {
      return Failure("wrong number of arguments in call to procedure " + name);
    }
    assert |args| == |rawProc.parameters|;

    var aa: seq<CallArgument> := [];
    for n := 0 to |args|
      invariant forall i :: 0 <= i < n ==> args[i].mode == rawProc.parameters[i].mode
      invariant forall i :: 0 <= i < n ==> args[i].arg.WellFormed(prs.ers.b3, ls.varMap.Keys)
      invariant |aa| == n
      invariant forall i :: 0 <= i < n ==> aa[i].CorrespondingMode() == proc.Parameters[i].mode && aa[i].WellFormed()
    {
      if args[n].mode != proc.Parameters[n].mode {
        return Failure("mismatched parameter mode in call to procedure " + name);
      }
      var e :- ResolveExpr(args[n].arg, prs.ers, ls.varMap);
      var ca;
      if args[n].mode == Raw.In {
        ca := InArgument(e);
      } else if !e.IdExpr? {
        return Failure(Printer.ParameterMode(args[n].mode) + "argument must be a variable");
      } else {
        ca := OutgoingArgument(args[n].mode == Raw.InOut, e.v);
      }
      aa := aa + [ca];
    }

    return Success(Call(proc, aa));
  }

  function PrependAssumption(expr: Expr, stmt: Stmt): (r: Stmt)
    requires expr.WellFormed() && stmt.WellFormed()
    ensures r.WellFormed()
  {
    if stmt.Block? then
      Block([Assume(expr)] + stmt.stmts)
    else
      Block([Assume(expr), stmt])
  }

  method ResolveAExprs(aexprs: seq<Raw.AExpr>, ers: ExprResolverState, ls: LocalResolverState) returns (r: Result<seq<AExpr>, string>)
    requires ers.Valid()
    ensures r.Success? ==> forall ae <- aexprs :: ae.WellFormed(ers.b3, ers.generatedTypes, ls.varMap.Keys)
    ensures r.Success? ==> forall ae <- r.value :: ae.WellFormed()
  {
    var result := [];
    for n := 0 to |aexprs|
      invariant forall ae <- aexprs[..n] :: ae.WellFormed(ers.b3, ers.generatedTypes, ls.varMap.Keys)
      invariant forall ae: AExpr <- result :: ae.WellFormed()
    {
      var ae :- ResolveAExpr(aexprs[n], ers, ls);
      result := result + [ae];
    }
    return Success(result);
  }

  method ResolveAExpr(aexpr: Raw.AExpr, ers: ExprResolverState, ls: LocalResolverState) returns (r: Result<AExpr, string>)
    requires ers.Valid()
    ensures r.Success? ==> aexpr.WellFormed(ers.b3, ers.generatedTypes, ls.varMap.Keys)
    ensures r.Success? ==> r.value.WellFormed()
  {
    match aexpr
    case AExpr(e) =>
      var expr :- ResolveExpr(e, ers, ls.varMap);
      var location := new Location("check " + expr.ToString());
      return Success(AExpr(expr, location));
    case AAssertion(s) =>
      var prs := ProcResolverState(ers, None);
      var stmt :- ResolveStmt(s, prs, ls.(labelMap := map[], loopLabel := None));
      return Success(AAssertion(stmt));
  }
}