module Printer {
  import opened Std.Wrappers
  import opened Basics
  import opened PrintUtil
  import opened RawAst
  import Types

  method Program(b3: Program) {
    print "// B3 program\n";
    for i := 0 to |b3.types| {
      print "\n";
      TypeDecl(b3.types[i]);
    }
    for i := 0 to |b3.taggers| {
      print "\n";
      TaggerDecl(b3.taggers[i]);
    }
    for i := 0 to |b3.functions| {
      print "\n";
      FunctionDecl(b3.functions[i]);
    }
    for i := 0 to |b3.axioms| {
      print "\n";
      AxiomDecl(b3.axioms[i]);
    }
    for i := 0 to |b3.procedures| {
      print "\n";
      Procedure(b3.procedures[i]);
    }
  }

  method TypeDecl(ty: Types.TypeName) {
    print "type ", ty, "\n";
  }

  method TaggerDecl(tagger: Tagger) {
    print "tagger ", tagger.name, " for ", tagger.typ, "\n";
  }

  method FunctionDecl(func: Function) {
    print "function ", func.name, "(";
    var params := func.parameters;
    var sep := "";
    for i := 0 to |params| {
      var param := params[i];
      print sep, if param.injective then "injective " else "", param.name, ": ", param.typ;
      sep := ", ";
    }
    print "): ", func.resultType;
    if func.tag.Some? {
      print " tag ", func.tag.value;
    }
    print "\n";

    if func.definition.Some? {
      var FunctionDefinition(when, body) := func.definition.value;
      for i := 0 to |when| {
        Indent(IndentAmount);
        print "when ";
        Expression(when[i]);
        print "\n";
      }

      print "{\n";
      Indent(IndentAmount);
      Expression(body, MultipleLines(IndentAmount));
      print "\n}\n";
    }
  }

  method AxiomDecl(axiom: Axiom) {
    print "axiom";
    var prefix := " explains ";
    for i := 0 to |axiom.explains| {
      print prefix, axiom.explains[i];
      prefix := ", ";
    }
    print "\n";
    Indent(IndentAmount);
    Expression(axiom.expr, MultipleLines(IndentAmount));
    print "\n";
  }

  method Procedure(proc: Procedure) {
    print "procedure ", proc.name, "(";
    var params := proc.parameters;
    var sep := "";
    for i := 0 to |params| {
      var param := params[i];
      print sep, ParameterMode(param.mode), param.name, ": ", param.typ;
      sep := ", ";
    }
    print ")\n";

    PrintAExprs(IndentAmount, "requires", proc.pre);
    PrintAExprs(IndentAmount, "ensures", proc.post);

    match proc.body
    case None =>
    case Some(stmt) => StmtAsBlock(stmt, 0);
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
      print lhs, " := ";
      Expression(rhs);
      print "\n";

    case Block(stmts) =>
      print "{\n";
      StatementList(stmts, indent + IndentAmount);
      Indent(indent);
      print "}\n";

    case Call(proc, args) =>
      print proc, "(";
      var sep := "";
      for i := 0 to |args| {
        print sep, ParameterMode(args[i].mode);
        Expression(args[i].arg);
        sep := ", ";
      }
      print ")\n";

    case Check(e) =>
      ExpressionStmt("check", e);

    case Assume(e) =>
      ExpressionStmt("assume", e);

    case Assert(e) =>
      ExpressionStmt("assert", e);

    case AForall(name, typ, body) =>
      print "forall ", name, ": ", typ, " ";
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
      
    case If(cond, thn, els) =>
      print "if ";
      Expression(cond);
      print " ";
      if els.IsEmptyBlock() {
        StmtAsBlock(thn, indent);
      } else {
        StmtAsBlock(thn, indent, " else ");
        if els.If? || els.IfCase? {
          Statement(els, indent, omitInitialIndent := true);
        } else {
          StmtAsBlock(els, indent);
        }
      }

    case IfCase(cases) =>
      print "if ";
      if |cases| == 0 {
        Indent(indent);
        print "case false {\n";
        Indent(indent);
        print "}\n";
      } else {
        for i := 0 to |cases| {
          var cs := cases[i];
          print "case ";
          Expression(cs.cond);
          print " ";
          StmtAsBlock(cs.body, indent, if i == |cases| - 1 then "\n" else " ");
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
      print lbl, ": ";
      if body.Loop? {
        Statement(body, indent, omitInitialIndent := true);
      } else {
        StmtAsBlock(body, indent);
      }

    case Exit(lbl) =>
      print "exit";
      if lbl.Some? {
        print " ", lbl.value;
      }
      print "\n";

    case Return =>
      print "return\n";

    case Probe(e) =>
      ExpressionStmt("probe", e);
  }

  method VariableDeclaration(v: Variable, init: Option<Expr>, body: Stmt, indent: nat, followedByEndCurly: bool)
    decreases body, 3
  {
    IdTypeDecl(if v.isMutable then "var " else "val ", v.name, v.optionalType);
    match init {
      case None =>
      case Some(e) =>
        print " := ";
        Expression(e);
    }
    print "\n";
    BlockAsStatementList(body, indent, followedByEndCurly);
  }

  method Bindings(prefix: string, bindings: seq<Binding>) {
    var prefix := prefix;
    for i := 0 to |bindings| {
      IdTypeDecl(prefix, bindings[i].name, Some(bindings[i].typ));
      prefix := ", ";
    }
  }

  method IdTypeDecl(prefix: string, name: string, optionalType: Option<Types.TypeName>) {
    print prefix, name;
    match optionalType
    case None =>
    case Some(typ) => print ": ", typ;
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

  method PrintAExprs(indent: nat, prefix: string, aexprs: seq<AExpr>, ghost parent: Stmt := Loop(aexprs, Return))
    requires forall ae <- aexprs :: ae.AAssertion? ==> ae.s < parent
    decreases parent, 0
  {
    for i := 0 to |aexprs| {
      Indent(indent);
      print prefix, " ";
      match aexprs[i]
      case AExpr(e) =>
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
  method Expression(expr: Expr, format: ExprFormatOption := SingleLine) {
    // TODO: add parentheses around the entire expression when necessary
    match expr
    case BLiteral(value) => print value;
    case ILiteral(value) => print value;
    case CustomLiteral(s, typ) => print "|", s, ": ", typ, "|";
    case IdExpr(name) => print name;
    case OperatorExpr(op, args) =>
      if op == IfThenElse && op.ArgumentCount() == |args| {
        var ind := format.More();
        print "if ";
        Expression(args[0]);
        print " then";
        ind.Space();
        Expression(args[1], ind);
        format.Space();
        print "else";
        if args[2].OperatorExpr? && args[2].op == IfThenElse {
          // print as cascading if
          print " ";
          Expression(args[2], format);
        } else {
          ind.Space();
          Expression(args[2], ind);
        }
      } else if op.ArgumentCount() == 1 == |args| {
        print op.ToString();
        Expression(args[0]);
      } else if op.ArgumentCount() == 2 == |args| {
        Expression(args[0]);
        print " ", op.ToString();
        if op in {Operator.LogicalImp, Operator.LogicalAnd, Operator.LogicalOr} {
          format.Space();
          Expression(args[1], format);
        } else {
          print " ";
          Expression(args[1]);
        }
      } else {
        print op.ToString(), "(";
        ExpressionList(args);
        print ")";
      }
    case FunctionCallExpr(name, args) =>
      print name, "(";
      ExpressionList(args);
      print ")";
    case LabeledExpr(name, body) =>
      print name, ": ";
      Expression(body, format);
    case LetExpr(name, optionalType, rhs, body) =>
      IdTypeDecl("val ", name, optionalType);
      print " := ";
      Expression(rhs);
      format.Space();
      Expression(body, format);
    case QuantifierExpr(univ, bindings, patterns, body) =>
      Bindings(if univ then "forall " else "exists ", bindings);
      var ind := format.More();
      if patterns != [] {
        for i := 0 to |patterns| {
          ind.Space();
          print "pattern ";
          ExpressionList(patterns[i].exprs);
        }
      }
      ind.Space();
      Expression(body, ind);
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
