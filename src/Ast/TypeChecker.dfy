module TypeChecker {
  export
    provides TypeCheck, TypeCorrect
    provides Wrappers, Ast

  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import opened Ast
  import Printer

  method TypeCheck(b3: Program) returns (outcome: Outcome<string>)
    requires b3.WellFormed()
    ensures outcome.Pass? ==> TypeCorrect(b3)
  {
    // Nothing to check for type declarations and tagger declarations

    for n := 0 to |b3.functions|
      invariant forall func <- b3.functions[..n] :: TypeCorrectFunction(func)
    {
      :- CheckFunction(b3.functions[n]);
    }

    for n := 0 to |b3.axioms|
      invariant forall axiom <- b3.axioms[..n] :: TypeCorrectAxiom(axiom)
    {
      var axiom := b3.axioms[n];
      assert axiom.WellFormed();
      :- TypeCheckAs(axiom.Expr, BoolType);
    }

    for n := 0 to |b3.procedures|
      invariant forall proc <- b3.procedures[..n] :: TypeCorrectProc(proc)
    {
      :- CheckProcedure(b3.procedures[n]);
    }

    return Pass;
  }

  predicate TypeCorrect(b3: Program)
    requires b3.WellFormed()
    reads b3.functions, b3.procedures
  {
    && (forall func <- b3.functions :: TypeCorrectFunction(func))
    && (forall axiom <- b3.axioms :: TypeCorrectAxiom(axiom))
    && (forall proc <- b3.procedures :: TypeCorrectProc(proc))
  }

  predicate TypeCorrectFunction(func: Function)
    requires func.WellFormed()
    reads func
  {
    match func.Definition
    case None => true
    case Some(def) =>
      && (forall e <- def.when :: TypeCorrectExpr(e) && e.HasType(BoolType))
      && TypeCorrectExpr(def.body)
      && def.body.HasType(func.ResultType)
  }

  predicate TypeCorrectAxiom(axiom: Axiom)
    requires axiom.WellFormed()
  {
    TypeCorrectExpr(axiom.Expr) && axiom.Expr.HasType(BoolType)
  }

  predicate TypeCorrectProc(proc: Procedure)
    requires proc.WellFormed()
    reads proc
  {
    // TODO: to include the following line, the parameters need to be added to the "reads" clause
    // && (forall p <- proc.Parameters :: p.maybeAutoInv.Some? ==> TypeCorrectExpr(p.maybeAutoInv.value) && p.maybeAutoInv.value.HasType(BoolType))
    && (forall ae <- proc.Pre :: TypeCorrectAExpr(ae))
    && (forall ae <- proc.Post :: TypeCorrectAExpr(ae))
    && (proc.Body.Some? ==> TypeCorrectStmt(proc.Body.value))
  }

  predicate TypeCorrectAExpr(aexpr: AExpr)
    requires aexpr.WellFormed()
  {
    match aexpr
    case AExpr(e, _) =>
      TypeCorrectExpr(e) && e.HasType(BoolType)
    case AAssertion(s) =>
      TypeCorrectStmt(s)
  }

  predicate TypeCorrectStmt(stmt: Stmt)
    requires stmt.WellFormed()
  {
    match stmt
    case VarDecl(variable, init, body) =>
      && (init.Some? ==> TypeCorrectExpr(init.value))
      // TODO: to include the following line, all local variables need to be added to the "reads" clause
      // && (variable.maybeAutoInv.Some? ==> TypeCorrectExpr(variable.maybeAutoInv.value) && variable.maybeAutoInv.value.HasType(BoolType))
      && TypeCorrectStmt(body)
    case Assign(lhs, rhs) =>
      TypeCorrectExpr(rhs) && rhs.HasType(lhs.typ)
    case Reinit(_) =>
      true
    case Block(stmts) =>
      forall s <- stmts :: TypeCorrectStmt(s)
    case Call(proc, args) =>
      forall arg <- args :: TypeCorrectCallArg(arg)
    case Check(cond, _) =>
      TypeCorrectExpr(cond)
    case Assume(cond) =>
      TypeCorrectExpr(cond)
    case Reach(cond, _) =>
      TypeCorrectExpr(cond)
    case Assert(cond, _) =>
      TypeCorrectExpr(cond)
    case AForall(_, body) =>
      TypeCorrectStmt(body)
    case Choose(branches) =>
      forall branch <- branches :: TypeCorrectStmt(branch)
    case Loop(invariants, body) =>
      && (forall inv <- invariants :: TypeCorrectAExpr(inv))
      && TypeCorrectStmt(body)
    case LabeledStmt(_, body) =>
      TypeCorrectStmt(body)
    case Exit(_) =>
      true
    case Probe(expr) =>
      TypeCorrectExpr(expr)
  }

  predicate TypeCorrectCallArg(arg: CallArgument)
    requires arg.WellFormed()
  {
    match arg
    case InArgument(e) => TypeCorrectExpr(e)
    case OutgoingArgument(_, _) => true
  }

  predicate TypeCorrectExpr(expr: Expr)
    requires expr.WellFormed()
  {
    match expr
    case BLiteral(_) => true
    case ILiteral(_) => true
    case CustomLiteral(_, _) => true
    case IdExpr(_) => true
    case OperatorExpr(op, args) =>
      && (forall arg <- args :: TypeCorrectExpr(arg))
      && match op {
          case IfThenElse =>
            args[0].HasType(BoolType) && args[1].ExprType() == args[2].ExprType()
          case Equiv | LogicalImp | LogicalAnd | LogicalOr =>
            args[0].HasType(BoolType) && args[1].HasType(BoolType)
          case Eq | Neq =>
            args[0].ExprType() == args[1].ExprType()
          case Less | AtMost | Plus | Minus | Times | Div | Mod =>
            args[0].HasType(IntType) && args[1].HasType(IntType)
          case LogicalNot =>
            args[0].HasType(BoolType)
          case UnaryMinus =>
            args[0].HasType(IntType)
      }
    case FunctionCallExpr(func, args) =>
      forall i :: 0 <= i < |args| ==> TypeCorrectExpr(args[i]) && args[i].HasType(func.Parameters[i].typ)
    case LabeledExpr(lbl, body) =>
      TypeCorrectExpr(body)
    case LetExpr(v, rhs, body) =>
      rhs.HasType(v.typ) && TypeCorrectExpr(body)
    case QuantifierExpr(_, _, patterns, body) =>
      (forall tr <- patterns, e <- tr.exprs :: assert tr.WellFormed(); TypeCorrectExpr(e)) &&
      TypeCorrectExpr(body) && body.HasType(BoolType)
    case ClosureExpr(_, _, _, _) =>
      // Closures must be elaborated before type checking
      false
  }

  method CheckFunction(func: Function) returns (outcome: Outcome<string>)
    requires func.WellFormed()
    ensures outcome.Pass? ==> TypeCorrectFunction(func)
  {
    match func.Definition {
      case None =>
      case Some(def) =>
        for n := 0 to |def.when|
          invariant forall e <- def.when[..n] :: TypeCorrectExpr(e) && e.HasType(BoolType)
        {
          :- TypeCheckAs(def.when[n], BoolType);
        }
        :- TypeCheckAs(def.body, func.ResultType);
    }
    return Pass;
  }

  method CheckProcedure(proc: Procedure) returns (outcome: Outcome<string>)
    requires proc.WellFormed()
    ensures outcome.Pass? ==> TypeCorrectProc(proc)
  {
    for n := 0 to |proc.Parameters| {
      var p := proc.Parameters[n];
      if p.maybeAutoInv.Some? {
        assume {:axiom} p.maybeAutoInv.value.WellFormed(); // TODO: to add this condition to WellFormed, all AutoInvVariable's need to be added to the "reads" clause
        :- TypeCheckAs(p.maybeAutoInv.value, BoolType);
      }
    }
    :- CheckAExprs(proc.Pre);
    :- CheckAExprs(proc.Post);
    if proc.Body.Some? {
      :- CheckStmt(proc.Body.value);
    }
    return Pass;
  }

  method CheckAExprs(aexprs: seq<AExpr>) returns (outcome: Outcome<string>)
    requires forall ae <- aexprs :: ae.WellFormed()
    ensures outcome.Pass? ==> forall ae <- aexprs :: TypeCorrectAExpr(ae)
  {
    for n := 0 to |aexprs|
      invariant forall ae <- aexprs[..n] :: TypeCorrectAExpr(ae)
    {
      assert aexprs[n].WellFormed();
      match aexprs[n]
      case AExpr(e, _) =>
        outcome := TypeCheckAs(e, BoolType);
        if outcome.IsFailure() {
          return Fail(outcome.error);
        }
      case AAssertion(s) =>
        assert aexprs decreases to s by {
          assert aexprs decreases to aexprs[n];
          assert aexprs[n] decreases to s;
        }
        :- CheckStmt(s);
    }
    return Pass;
  }

  method TypeCheckAs(expr: Expr, expectedType: Type) returns (outcome: Outcome<string>)
    requires expr.WellFormed()
    ensures outcome.Pass? ==> TypeCorrectExpr(expr) && expr.HasType(expectedType)
  {
    var r := CheckExpr(expr);
    if r.IsFailure() {
      return r.ToOutcome();
    }
    var typ := r.value;
    outcome := ExpectType(typ, expectedType);
  }

  method ExpectType(typ: Type, expectedType: Type) returns (outcome: Outcome<string>)
    ensures outcome.Pass? ==> typ == expectedType
  {
    if typ != expectedType {
      return Fail("expect type '" + expectedType.ToString() + "', got type '" + typ.ToString() + "'");
    }
    return Pass;
  }

  method CheckStmt(stmt: Stmt) returns (outcome: Outcome<string>)
    requires stmt.WellFormed()
    ensures outcome.Pass? ==> TypeCorrectStmt(stmt)
  {
    match stmt {
      case VarDecl(variable, init, body) =>
        if variable.maybeAutoInv.Some? {
          assume {:axiom} variable.maybeAutoInv.value.WellFormed(); // TODO: to add this condition to WellFormed, all AutoInvVariable's need to be added to the "reads" clause
          :- TypeCheckAs(variable.maybeAutoInv.value, BoolType);
        }
        if init.Some? {
          :- TypeCheckAs(init.value, variable.typ);
        }
        :- CheckStmt(body);
      case Assign(lhs, rhs) =>
        :- TypeCheckAs(rhs, lhs.typ);
      case Reinit(_) =>
      case Block(stmts) =>
        for n := 0 to |stmts|
          invariant forall s <- stmts[..n] :: TypeCorrectStmt(s)
        {
          :- CheckStmt(stmts[n]);
        }
      case Call(proc, args) =>
        for n := 0 to |args|
          invariant forall arg <- args[..n] :: TypeCorrectCallArg(arg)
        {
          var formal := proc.Parameters[n];
          assert args[n].WellFormed();
          match args[n]
          case InArgument(e) =>
            :- TypeCheckAs(e, formal.typ);
          case OutgoingArgument(_, arg) =>
            :- ExpectType(arg.typ, formal.typ);
        }
      case Check(cond, _) =>
        :- TypeCheckAs(cond, BoolType);
      case Assume(cond) =>
        :- TypeCheckAs(cond, BoolType);
      case Reach(cond, _) =>
        :- TypeCheckAs(cond, BoolType);
      case Assert(cond, _) =>
        :- TypeCheckAs(cond, BoolType);
      case AForall(_, body) =>
        :- CheckStmt(body);
      case Choose(branches) =>
        for n := 0 to |branches|
          invariant forall branch <- branches[..n] :: TypeCorrectStmt(branch)
        {
          :- CheckStmt(branches[n]);
        }
      case Loop(invariants, body) =>
        :- CheckAExprs(invariants);
        :- CheckStmt(body);
      case LabeledStmt(_, body) =>
        :- CheckStmt(body);
      case Exit(_) =>
      case Probe(expr) =>
        var r := CheckExpr(expr);
        if r.IsFailure() {
          return r.ToOutcome();
        }
    }
    return Pass;
  }

  method CheckExpr(expr: Expr) returns (r: Result<Type, string>)
    requires expr.WellFormed()
    ensures r.Success? ==> TypeCorrectExpr(expr) && expr.HasType(r.value)
  {
    match expr
    case BLiteral(_) =>
      return Success(BoolType);
    case ILiteral(_) =>
      return Success(IntType);
    case CustomLiteral(_, typ) =>
      return Success(typ);
    case IdExpr(v) =>
      return Success(v.typ);
    case OperatorExpr(op, args) =>
      var types :- CheckExprList(args);
      var typ;
      match op {
        case IfThenElse =>
          if types[0] != BoolType {
            return Result<Type, string>.Failure(
              "if condition must have type '" + BoolTypeName + "'; got '" + types[0].ToString() + "'");
          }
          if types[1] != types[2] {
            return Result<Type, string>.Failure(
              "if-then-else expression requires the then-branch and else-branche to have the same type; got '" +
              types[1].ToString() + "' and '" + types[2].ToString() + "'");
          }
          typ := types[1];
        case Equiv | LogicalImp | LogicalAnd | LogicalOr | LogicalNot =>
          var _ :- ExpectOperandTypes(op, types, BoolType);
          typ := BoolType;
        case Eq | Neq =>
          if types[0] != types[1] {
            return Result<Type, string>.Failure(
              "operator " + op.ToString() + " requires both arguments to have the same type; got '" +
              types[0].ToString() + "' and '" + types[1].ToString() + "'");
          }
          typ := BoolType;
        case Less | AtMost =>
          var _ :- ExpectOperandTypes(op, types, IntType);
          typ := BoolType;
        case Plus | Minus | Times | Div | Mod | UnaryMinus =>
          var _ :- ExpectOperandTypes(op, types, IntType);
          typ := IntType;
      }
      return Success(typ);
    case FunctionCallExpr(func, args) =>
      for n := 0 to |args|
        invariant forall i :: 0 <= i < n ==> TypeCorrectExpr(args[i]) && args[i].HasType(func.Parameters[i].typ)
      {
        var typ :- CheckExpr(args[n]);
        var expectedType := func.Parameters[n].typ;
        if typ != expectedType {
          return Failure("parameter " + Int2String(n) + " to function '" + func.Name + "' expects type '" + expectedType.ToString() + "', got type '" + typ.ToString() + "'");
        }
      }
      return Success(func.ResultType);
    case LabeledExpr(_, body) =>
      r := CheckExpr(body);
    case LetExpr(v, rhs, body) =>
      var rhsType :- CheckExpr(rhs);
      if v.typ != rhsType {
        return Failure("types of bound variable and the RHS must agree; got " + v.typ.ToString() + " and " + rhsType.ToString());
      }
      r := CheckExpr(body);
    case QuantifierExpr(_, v, patterns, body) =>
      for m := 0 to |patterns|
        invariant forall tr <- patterns[..m], e <- tr.exprs :: assert tr.WellFormed(); TypeCorrectExpr(e)
      {
        var tr := patterns[m];
        assert tr.WellFormed();
        for n := 0 to |tr.exprs|
          invariant forall e <- tr.exprs[..n] :: TypeCorrectExpr(e)
        {
          var e := tr.exprs[n];
          var typ :- CheckExpr(e);
        }
      }
      var typ :- CheckExpr(body);
      if typ != BoolType {
        return Failure("body of quantifier expression must have type " + BoolTypeName + ", got " + typ.ToString());
      }
      return Success(typ);
    case ClosureExpr(_, _, _, _) =>
      return Failure("closure must be elaborated before type checking");
  }

  method CheckExprList(exprs: seq<Expr>) returns (r: Result<seq<Type>, string>)
    requires forall expr <- exprs :: expr.WellFormed()
    ensures r.Success? ==> forall expr <- exprs :: TypeCorrectExpr(expr)
    ensures r.Success? ==> |r.value| == |exprs|
    ensures r.Success? ==> forall i :: 0 <= i < |exprs| ==> exprs[i].HasType(r.value[i])
  {
    var types := [];
    for n := 0 to |exprs|
      invariant forall expr <- exprs[..n] :: TypeCorrectExpr(expr)
      invariant |types| == n
      invariant forall i :: 0 <= i < n ==> exprs[i].HasType(types[i])
    {
      var typ :- CheckExpr(exprs[n]);
      types := types + [typ];
    }
    return Success(types);
  }

  method ExpectOperandTypes(op: Operator, operandTypes: seq<Type>, expectedType: Type) returns (r: Result<(), string>)
    ensures r.Success? ==> operandTypes == seq(|operandTypes|, _ => expectedType)
  {
    if i :| 0 <= i < |operandTypes| && operandTypes[i] != expectedType {
      if operandTypes[i] != expectedType {
        return Result<(), string>.Failure(
          "operands of " + op.ToString() + " must have type '" +
          expectedType.ToString() + "'; got '" + operandTypes[i].ToString() + "'");
      }
    }
    return Success(());
  }
}