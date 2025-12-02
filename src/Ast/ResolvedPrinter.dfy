module ResolvedPrinter {
  import opened Std.Wrappers
  import opened Basics
  import opened PrintUtil
  import opened Ast
  import Types

  method Program(b3: Program) {
    print "// Resolved B3 program\n";

    for i := 0 to |b3.types| {
      var typ := b3.types[i];
      print "\n";
      TypeDecl(typ);
    }

    for i := 0 to |b3.functions| {
      var func := b3.functions[i];
      print "\n";
      FunctionDecl(func);
    }

    for i := 0 to |b3.axioms| {
      print "\n";
      AxiomDecl(b3.axioms[i]);
    }

    for i := 0 to |b3.procedures| {
      var proc := b3.procedures[i];
      print "\n";
      Procedure(proc);
    }
  }

  method TypeDecl(decl: TypeDecl) {
    print "type ", decl.Name, "\n";
  }

  method FunctionDecl(func: Function) {
    print "function ", func.Name, "(";
    var params := func.Parameters;
    var sep := "";
    for i := 0 to |params| {
      var param := params[i];
      print sep, if param.injective then "injective " else "", param.name, ": ", param.typ.ToString();
      sep := ", ";
    }
    print "): ", func.ResultType.ToString();
    if func.Tag.Some? {
      print " tag ", func.Tag.value.Name;
    }
    print "\n";

    if func.Definition.Some? {
      var FunctionDefinition(when, body) := func.Definition.value;
      for i := 0 to |when| {
        Indent(IndentAmount);
        print "when ";
        Expression(when[i]);
        print "\n";
      }

      print "{\n";
      Indent(IndentAmount);
      Expression(body, format := MultipleLines(IndentAmount));
      print "\n}\n";
    }
  }

  method AxiomDecl(axiom: Axiom) {
    print "axiom";
    var prefix := " explains ";
    for i := 0 to |axiom.Explains| {
      print prefix, axiom.Explains[i].Name;
      prefix := ", ";
    }
    print "\n";
    Indent(IndentAmount);
    Expression(axiom.Expr, format := MultipleLines(IndentAmount));
    print "\n";
  }

  method Procedure(proc: Procedure) {
    print "procedure ", proc.Name, "(";
    var params := proc.Parameters;
    var sep := "";
    for i := 0 to |params| {
      var param := params[i];
      print sep, ParameterMode(param.mode), param.name, ": ", param.typ.ToString();
      OptionalAutoInvariant(param.maybeAutoInv);
      sep := ", ";
    }
    print ")\n";

    PrintAExprs(IndentAmount, "requires", proc.Pre);
    PrintAExprs(IndentAmount, "ensures", proc.Post);

    match proc.Body
    case None =>
    case Some(body) => StmtAsBlock(body, 0);
  }

  method OptionalAutoInvariant(maybeAutoInv: Option<Expr>) {
    match maybeAutoInv
    case None =>
    case Some(autoInv) =>
      print " autoinv ";
      Expression(autoInv);
  }

  method Statement(stmt: Stmt, indent: nat, followedByEndCurly: bool := false, omitInitialIndent: bool := false)
    decreases stmt, 1
  {
    if !omitInitialIndent {
      Indent(indent);
    }

    match stmt
    case VarDecl(v, init, body) =>
      if followedByEndCurly {
        VariableDeclaration(v, init, body, indent, followedByEndCurly);
      } else {
        print "{\n";
        Indent(indent + IndentAmount);
        VariableDeclaration(v, init, body, indent + IndentAmount, true);
        Indent(indent);
        print "}\n";
      }

    case Assign(lhs, rhs) =>
      print lhs.name, " := ";
      Expression(rhs);
      print "\n";

    case Reinit(vars) =>
      print "reinit ";
      var sep := "";
      for i := 0 to |vars| {
        var v: Variable := vars[i];
        print sep, v.name;
        sep := ", ";
      }
      print "\n";

    case Block(stmts) =>
      print "{\n";
      StatementList(stmts, indent + IndentAmount);
      Indent(indent);
      print "}\n";

    case Call(proc, args) =>
      print proc.Name, "(";
      var sep := "";
      for i := 0 to |args| {
        print sep;
        sep := ", ";
        match args[i]
        case InArgument(e) =>
          Expression(e);
        case OutgoingArgument(isInOut, v) =>
          print if isInOut then "inout " else "out ", v.name;
      }
      print ")\n";

    case Check(e, _) =>
      ExpressionStmt("check", e);

    case Assume(e) =>
      ExpressionStmt("assume", e);

    case Reach(e, _) =>
      ExpressionStmt("reach", e);

    case Assert(e, _) =>
      ExpressionStmt("assert", e);

    case AForall(v, body) =>
      print "forall ", v.name, ": ", v.typ.ToString(), " ";
      StmtAsBlock(body, indent);

    case Choose(branches) =>
      print "choose ";
      if |branches| == 0 {
        print "{ }\n";
      } else {
        for i := 0 to |branches| {
          StmtAsBlock(branches[i], indent, if i == |branches| - 1 then "\n" else " or ");
        }
      }
      
    case Loop(invariants, body) =>
      print "loop";
      if |invariants| == 0 {
        print " ";
      } else {
        print "\n";
        PrintAExprs(indent + IndentAmount, "invariant", invariants, stmt);
        Indent(indent);
      }
      StmtAsBlock(body, indent);

    case LabeledStmt(lbl, body) =>
      print lbl.Name, ": ";
      if body.Loop? {
        Statement(body, indent, omitInitialIndent := true);
      } else {
        StmtAsBlock(body, indent);
      }

    case Exit(lbl) =>
      print "exit ", lbl.Name, "\n";

    case Probe(e) =>
      ExpressionStmt("probe", e);
  }

  method VariableDeclaration(v: Variable, init: Option<Expr>, body: Stmt, indent: nat, followedByEndCurly: bool)
    decreases body, 3
  {
    IdTypeDecl(if v.IsMutable() then "var " else "val ", v.name, v.typ);
    if v is AutoInvVariable {
      OptionalAutoInvariant((v as AutoInvVariable).maybeAutoInv);
    }
    match init {
      case None =>
      case Some(e) =>
        print " := ";
        Expression(e);
    }
    print "\n";
    BlockAsStatementList(body, indent, followedByEndCurly);
  }

  method Bindings(prefix: string, vv: seq<Variable>) {
    var prefix := prefix;
    for i := 0 to |vv| {
      IdTypeDecl(prefix, vv[i].name, vv[i].typ);
      prefix := ", ";
    }
  }

  method IdTypeDecl(prefix: string, name: string, typ: Type) {
    print prefix, name, ": ", typ.ToString();
  }

  method StmtAsBlock(stmt: Stmt, indent: nat, suffix: string := "\n")
    decreases stmt
  {
    print "{\n"; // always omits initial indent
    match stmt {
      case Block(stmts) =>
        // omit the braces of the Block itself, since we're already printing braces
        StatementList(stmts, indent + IndentAmount);
      case _ =>
        Statement(stmt, indent + IndentAmount);
    }
    Indent(indent);
    print "}", suffix;
  }

  method BlockAsStatementList(stmt: Stmt, indent: nat, followedByEndCurly: bool)
    decreases stmt, 2
  {
    match stmt
    case Block(stmts) =>
      StatementList(stmts, indent);
    case _ =>
      Statement(stmt, indent, followedByEndCurly);
  }

  method StatementList(stmts: seq<Stmt>, indent: nat, followedByEndCurly: bool := true) {
    for i := 0 to |stmts| {
      Statement(stmts[i], indent, followedByEndCurly && i == |stmts| - 1);
    }
  }

  function ParameterMode(mode: ParameterMode): string {
    match mode
    case InOut => "inout "
    case Out => "out "
    case _ => ""
  }

  method PrintAExprs(indent: nat, prefix: string, aexprs: seq<AExpr>, ghost parent: Stmt := Loop(aexprs, Block([])))
    requires forall ae <- aexprs :: ae.AAssertion? ==> ae.s < parent
    decreases parent, 0
  {
    for i := 0 to |aexprs| {
      Indent(indent);
      print prefix, " ";
      match aexprs[i]
      case AExpr(e, _) =>
        Expression(e);
        print "\n";
      case AAssertion(s) =>
        Statement(s, indent, omitInitialIndent := true);
    }
  }

  method ExpressionStmt(prefix: string, e: Expr) {
    print prefix, " ";
    Expression(e);
    print "\n";
  }

  // Print "expr" starting from the current position and ending without a final newline.
  // If "format" allows, break lines at an indent of "format.indent".
  method Expression(expr: Expr, context: BindingPower := BindingPower.Init, format: ExprFormatOption := SingleLine) {
    match expr
    case BLiteral(value) => print value;
    case ILiteral(value) => print value;
    case CustomLiteral(s, typ) => print CustomLiteralToString(s, typ.ToString());
    case IdExpr(v) =>
      match Raw.FromOldName(v.name) {
        case None => print v.name;
        case Some(origName) => print "old ", origName;
      }
    case OperatorExpr(op, args) =>
      var opStrength := op.BindingStrength();
      Parenthesis(Side.Left, opStrength, context);
      if op == Operator.IfThenElse && op.ArgumentCount() == |args| {
        var ind := format.More();
        print "if ";
        Expression(args[0]);
        ind.Space();
        Expression(args[1], format := ind);
        format.Space();
        print "else";
        if args[2].OperatorExpr? && args[2].op == Operator.IfThenElse {
          // print as cascading if
          print " ";
          Expression(args[2], opStrength.SubexpressionPower(Side.Right, context), format := format);
        } else {
          ind.Space();
          Expression(args[2], opStrength.SubexpressionPower(Side.Right, context), format := ind);
        }
      } else if op.ArgumentCount() == 1 == |args| {
        print op.ToString();
        Expression(args[0], opStrength.SubexpressionPower(Side.Right, context));
      } else if op.ArgumentCount() == 2 == |args| {
        Expression(args[0], opStrength.SubexpressionPower(Side.Left, context));
        print " ", op.ToString();
        if op in {Operator.LogicalImp, Operator.LogicalAnd, Operator.LogicalOr} {
          format.Space();
          Expression(args[1], opStrength.SubexpressionPower(Side.Right, context), format := format);
        } else {
          print " ";
          Expression(args[1], opStrength.SubexpressionPower(Side.Right, context));
        }
      } else {
        print op.ToString(), "(";
        ExpressionList(args);
        print ")";
      }
      Parenthesis(Side.Right, opStrength, context);
    case FunctionCallExpr(func, args) =>
      print func.Name, "(";
      ExpressionList(args);
      print ")";
    case LabeledExpr(lbl, body) =>
      var opStrength := BindingPower.EndlessOperator;
      Parenthesis(Side.Left, opStrength, context);
      print lbl.Name, ": ";
      Expression(body, opStrength.SubexpressionPower(Side.Right, context), format := format);
      Parenthesis(Side.Right, opStrength, context);
    case LetExpr(v, rhs, body) =>
      var opStrength := BindingPower.EndlessOperator;
      Parenthesis(Side.Left, opStrength, context);
      IdTypeDecl("val ", v.name, v.typ);
      print " := ";
      Expression(rhs);
      format.Space();
      Expression(body, opStrength.SubexpressionPower(Side.Right, context), format := format);
      Parenthesis(Side.Right, opStrength, context);
    case QuantifierExpr(univ, vv, patterns, body) =>
      var opStrength := BindingPower.EndlessOperator;
      Parenthesis(Side.Left, opStrength, context);
      Bindings(if univ then "forall " else "exists ", vv);
      var ind := format.More();
      for i := 0 to |patterns| {
        ind.Space();
        print "pattern ";
        ExpressionList(patterns[i].exprs);
      }
      ind.Space();
      Expression(body, opStrength.SubexpressionPower(Side.Right, context), format := ind);
      Parenthesis(Side.Right, opStrength, context);
    case ClosureExpr(_, _, _, _) =>
      // Closures must be elaborated before printing
      print "<closure-not-elaborated>";
  }

  method ExpressionList(exprs: seq<Expr>) {
    var sep := "";
    for i := 0 to |exprs| {
      print sep;
      sep := ", ";
      Expression(exprs[i]);
    }
  }
}
