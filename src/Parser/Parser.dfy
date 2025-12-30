module Parser {
  export
    provides TopLevel
    provides StringBuilders, RawAst

  import opened Std.Parsers.StringBuilders
  import opened Std.Wrappers
  import opened Basics
  import opened RawAst
  import Types
  import Std.Collections.Seq

  // Helpful error message about what it would have expected after repeatedly
  // parsing underlying
  function RepTill<T, U>(underlying: B<T>, consumeAfter: B<U>): B<seq<T>> {
    underlying.Rep().I_e(Or([consumeAfter.M(_ => ()), underlying.M(_ => ())]))
  }

  const TopLevel: B<Program> :=
    W.e_I(RepTill(parseTopLevelDecl.I_e(W), EOS)).M(
      decls =>
        var (tt, dd, gg, ff, aa, pp) := SeparateTopLevelDecls(decls);
        Program(tt, dd, gg, ff, aa, pp))

  // ----- Parser helpers

  // Parse `b`. If it succeeds, wrap `Some(_)`, reset the input, and return success.
  // If it fails with a recoverable error, return `None` and reset the input.
  // If it fails fatally, return the failure.
  function Lookahead<R>(b: B<R>): B<Option<R>> {
    B((input: Input) =>
        var p := b.apply(input);
        if p.IsFatalFailure() then
          P.ParseFailure(p.level, p.data)
        else if p.IsFailure() then
          P.ParseSuccess(None, input) // don't consume any input
        else
          P.ParseSuccess(Some(p.result), input) // don't consume any input
    )
  }

  // Parse `b`. If it succeeds, wrap `Some(_)` and return success.
  // If it fails with a recoverable error, return the failure, but reset the input.
  // If it fails fatally, return the failure.
  function Try<R>(b: B<R>): B<Option<R>> {
    B((input: Input) =>
        var p := b.apply(input);
        if p.IsFatalFailure() then
          P.ParseFailure(p.level, p.data)
        else if p.IsFailure() then
          P.ParseSuccess(None, input) // don't consume any input
        else
          P.ParseSuccess(Some(p.result), p.remaining) // consume input
    )
  }

  // Unless there's a fatal error in trying `b`, either perform all of `b` successfully
  // or return its failure without consuming input.
  function Atomic<R>(b: B<R>): B<R> {
    B((input: Input) =>
        var p := b.apply(input);
        if p.IsFailure() && !p.IsFatal() then
          P.ParseFailure(p.level, p.data.(remaining := input)) // reset input
        else
          p
    )
  }

  function ApplyUnlessFollowedBy<L, R>(main: B<L>, avoid: B<R>, errorMessage: string): B<L>
    // In short: act like "main", unless "avoid" succeeds after applying "main".
    // In detail:
    // Apply "main" and return its result, if
    //   -- the main application fails, or if
    //   -- the main application succeeds and subsequently applying "avoid" fails recoverably.
    // If the main application and the subsequent application of "avoid" both succeed, then
    // roll back both and report "errorMessage" as a recoverable eror.
    // If the main application succeeds and the subsequence application of "avoid" fails fatally,
    // return the fatal error.
  {
    B((input: Input) =>
        var (l, remaining) :- main.apply(input);
        match avoid.apply(remaining)
        case ParseFailure(Fatal, data) =>
          // propagate any fatal error
          P.ParseFailure(P.Fatal, data)
        case ParseFailure(Recoverable, data) =>
          // the bad thing did not happen, so return like "main" did
          P.ParseSuccess(l, remaining)
        case ParseSuccess(result, remaining) =>
          // the bad thing did happened, so unroll "main"
          P.ParseFailure(P.Recoverable, P.FailureData(errorMessage, input, None))
    )
  }

  const notNewline :=
    CharTest((c: char) => c !in "\n", "anything except newline")

  function StringConcat(s: string, t: string): string { s + t }

  // W1 = whitespace or single-line comment
  const W1: B<string> :=
    WS.I_I(
      S("//").I_I(notNewline.Rep()).M2(MId, StringConcat)
      .I_I(O([S("\n"), EOS.M(x => "")])).M2(MId, StringConcat)
      .I_I(WS).M2(MId, StringConcat).Rep()
    ).M((wsMore: (string, seq<string>)) => wsMore.0 + Seq.Join(Seq.Map(MId, wsMore.1), ""))

  function PositionAfterEndOfLongComment(input: Input, start: nat := 0, end: nat := P.A.Length(input)): (len: nat)
    requires start <= end <= P.A.Length(input)
    ensures start <= len <= end
    decreases end - start
  {
    if end <= start + 2 then
      end
    else if P.A.CharAt(input, start) == '*' && P.A.CharAt(input, start + 1) == '/' then
      start + 2
    else if P.A.CharAt(input, start) == '/' && P.A.CharAt(input, start + 1) == '*' then
      var next := PositionAfterEndOfLongComment(input, start + 2, end);
      PositionAfterEndOfLongComment(input, next, end)
    else
      PositionAfterEndOfLongComment(input, start + 1, end)
  }

  const parseUntilEndOfLongComment: B<string> :=
    B((input: Input) =>
        var n := PositionAfterEndOfLongComment(input, 0, P.A.Length(input));
        P.ParseSuccess(P.A.Slice(input, 0, n).View(), P.A.Drop(input, n))
    )

  // W = whitespace or comment
  const W: B<string> :=
    W1.I_I(
      S("/*").I_I(parseUntilEndOfLongComment).M2(MId, StringConcat)
      .I_I(W1).M2(MId, StringConcat).Rep()
    ).M((wsMore: (string, seq<string>)) => wsMore.0 + Seq.Join(Seq.Map(MId, wsMore.1), ""))

  const canStartIdentifierChar := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ%"
  const identifierChar := canStartIdentifierChar + "0123456789_$."
  const customLiteralChar := identifierChar + "+-*/@#!^"

  const parseIdentifierChar: B<char> := CharTest((c: char) => c in identifierChar, "identifier character")
  const parseIdentifierRaw: B<string> := // TODO: this should fail if the identifier is a keyword
    CharTest((c: char) => c in canStartIdentifierChar, "identifier start character").Then(
      (c: char) =>
        parseIdentifierChar.Rep().M((s: string) => [c] + s))
  const parseId: B<string> := parseIdentifierRaw.I_e(W)

  const parseCustomLiteralChar: B<char> := CharTest((c: char) => c in customLiteralChar, "custom literal character")
  const parseCustomLiteral: B<string> := parseCustomLiteralChar.Then((c: char) => parseCustomLiteralChar.Rep().M((s: string) => [c] + s))

  // T = token, that is, the string `s` followed by some non-identifier character (the non-identifier character is not consumed)
  // The characters in `s` are expected to be identifier characters
  function T(s: string): B<string> {
    ApplyUnlessFollowedBy(S(s), parseIdentifierChar, "keyword followed by identifier character")
    .I_e(W)
  }

  function Sym(s: string): B<string> {
    S(s).I_e(W)
  }

  function SymNotPrefix(s: string, suffixesToAvoid: seq<string>): B<string> {
    if suffixesToAvoid == [] then
      S(s).I_e(W)
    else
      B(P.Not(P.Lookahead(S(suffixesToAvoid[0]).apply))).e_I(SymNotPrefix(s, suffixesToAvoid[1..]))
  }

  function parseParenthesized<X>(parser: B<X>): B<X> {
    S("(").I_e(W).e_I(parser).I_e(S(")")).I_e(W)
  }

  function parseCommaDelimitedSeq<X>(parser: B<X>): B<seq<X>> {
    parser.RepSep(Sym(","))
  }

  function parseNonemptyCommaDelimitedSeq<X>(parser: B<X>): B<seq<X>> {
    parser.I_I(Sym(",").e_I(parser).Rep()).M2(MId, (x, xs) => [x] + xs)
  }

  function parseNonemptyBarDelimitedSeq<X>(parser: B<X>): B<seq<X>> {
    parser.I_I(Sym("|").e_I(parser).Rep()).M2(MId, (x, xs) => [x] + xs)
  }

  function Unfold3l<X, Y, Z>(r: ((X, Y), Z)): (X, Y, Z) {
    (r.0.0, r.0.1, r.1)
  }

  // ----- Top-level declarations

  datatype TopLevelDecl =
    | TType(typeDecl: Types.TypeName)
    | TDatatype(datatypeDecl: DatatypeDecl)
    | TTagger(taggerDecl: Tagger)
    | TFunction(funcDecl: Function)
    | TAxiom(axiomDecl: Axiom)
    | TProc(procDecl: Procedure)

  const parseTopLevelDecl: B<TopLevelDecl> :=
    Or([
         parseTypeDecl.M(decl => TType(decl)),
         parseDatatypeDecl.M(decl => TDatatype(decl)),
         parseTaggerDecl.M(decl => TTagger(decl)),
         parseFunctionDecl.M(decl => TFunction(decl)),
         parseAxiomDecl.M(decl => TAxiom(decl)),
         parseProcDecl.M(decl => TProc(decl))
       ])

  function SeparateTopLevelDecls(decls: seq<TopLevelDecl>): (seq<Types.TypeName>, seq<DatatypeDecl>, seq<Tagger>, seq<Function>, seq<Axiom>, seq<Procedure>) {
    if decls == [] then ([], [], [], [], [], []) else
      var (tt, dd, gg, ff, aa, pp) := SeparateTopLevelDecls(decls[1..]);
      match decls[0]
      case TType(decl) => ([decl] + tt, dd, gg, ff, aa, pp)
      case TDatatype(decl) => (tt, [decl] + dd, gg, ff, aa, pp)
      case TTagger(decl) => (tt, dd, [decl] + gg, ff, aa, pp)
      case TFunction(decl) => (tt, dd, gg, [decl] + ff, aa, pp)
      case TAxiom(decl) => (tt, dd, gg, ff, [decl] + aa, pp)
      case TProc(decl) => (tt, dd, gg, ff, aa, [decl] + pp)
  }

  const parseTypeDecl: B<Types.TypeName> :=
    T("type").e_I(parseId)

  const parseConstructorField: B<ConstructorField> :=
    parseIdType.M2(MId, (name, typ) => ConstructorField(name, typ))

  const parseConstructor: B<Constructor> :=
    parseId.Then(name =>
      parseParenthesized(parseCommaDelimitedSeq(parseConstructorField)).M(fields =>
        Constructor(name, fields)
      )
    )

  const parseDatatypeDecl: B<DatatypeDecl> :=
    T("datatype").e_I(parseId).Then(name =>
      Sym("=").e_I(parseNonemptyBarDelimitedSeq(parseConstructor)).M(constructors =>
        DatatypeDecl(name, constructors)
      )
    )

  const parseTaggerDecl: B<Tagger> :=
    T("tagger").e_I(parseId).I_e(T("for")).I_I(parseType).M2(MId, (name, typeName) => Tagger(name, typeName))

  const parseFunctionDecl: B<Function> :=
    T("function").e_I(parseId).Then(name =>
      parseParenthesized(parseCommaDelimitedSeq(parseFunctionFormal)).Then(formals =>
        Sym(":").e_I(parseType).Then(resultType =>
          T("tag").e_I(parseId).Option().Then(maybeTag =>
            parseFunctionDefinition.Option().M(maybeDefinition =>
              Function(name, formals, resultType, maybeTag, maybeDefinition)
    )))))

  const parseFunctionFormal: B<FParameter> :=
    T("injective").Option().M(opt => opt != None).Then(injective =>
      parseIdType.M2(MId, (name, typ) => FParameter(name, injective, typ))
    )

  const parseFunctionDefinition: B<FunctionDefinition> :=
    parseWhenClause.Rep().I_e(Sym("{")).I_I(parseExpr).I_e(Sym("}")).M2(MId, (when, body) => FunctionDefinition(when, body))

  const parseWhenClause: B<Expr> :=
    T("when").e_I(parseExpr)

  const parseAxiomDecl: B<Axiom> :=
    T("axiom")
    .e_I(T("explains").e_I(parseNonemptyCommaDelimitedSeq(parseId)).Option())
    .I_I(parseExpr).M2(MId, (explains, expr) => Axiom(if explains == None then [] else explains.value, expr))

  const parseProcDecl: B<Procedure> :=
    T("procedure")
    .e_I(parseId).Then(
      name =>
        parseParenthesized(parseCommaDelimitedSeq(parseProcFormal)).Then(
          formals =>
            var c := GetRecMapSel(stmtGallery);
            parseAExprSeq("requires", c).Then(
              pre =>
                parseAExprSeq("ensures", c).Then(
                  post =>
                    RecMap(stmtGallery, "block").Option().M(
                      optBody =>
                        Procedure(name, formals, pre, post, optBody)
                    )
                )
            )
        )
    )

  const parseParameterMode: B<ParameterMode> :=
    Or([
         T("inout").M(_ => ParameterMode.InOut),
         T("out").M(_ => ParameterMode.Out),
         Nothing.M(_ => ParameterMode.In)
       ])

  const parseProcFormal: B<PParameter> :=
    parseParameterMode.Then((mode: ParameterMode) =>
      parseIdType.Then((idType: (string, Types.TypeName)) =>
        var (name, typ) := idType;
          parseOptionalAutoInvariant.M(optionalAutoInv =>
            PParameter(name, mode, typ, optionalAutoInv))))

  const parseIdType: B<(string, Types.TypeName)> :=
    parseId.I_I(Sym(":").e_I(parseType))

  const parseIdOptionalType: B<(string, Option<Types.TypeName>)> :=
    parseId.I_I(SymNotPrefix(":", [":="]).e_I(parseType).Option())

  const parseType: B<Types.TypeName> :=
    Or([
      T("bool"),
      T("int"),
      T("tag"),
      parseId
    ])

  // ----- Parsing gallery

  type StmtRecSel = RecMapSel<Stmt>
  type ExprRecSel = RecMapSel<Expr>

  const stmtGallery: map<string, RecMapDef<Stmt>> :=
    map[
      "block" := RecMapDef(
        0, (c: StmtRecSel) =>
          Sym("{").e_I(RepTill(parseStmt(c), Sym("}"))).M(stmts => Block(stmts))),
      "stmt" := RecMapDef(1, (c: StmtRecSel) => parseStmt(c)),
      "if-cont" := RecMapDef(0, (c: StmtRecSel) => parseIfCont(c)),
      "loop" := RecMapDef(0, (c: StmtRecSel) => parseLoop(c))
    ]

  const exprGallery: map<string, RecMapDef<Expr>> :=
    map[
      "expr" := RecMapDef(1, (c: ExprRecSel) => parseEquivExpr(c))
    ]

  function GetRecMapSel<R(!new)>(underlying: map<string, RecMapDef<R>>): RecMapSel<R> {
    (fun: string) => RecMap(underlying, fun)
  }

  // ----- Statements

  function parseStmt(c: StmtRecSel): B<Stmt> {
    Or([
         T("var").e_I(parseVariableDeclaration(true, c)),
         T("val").e_I(parseVariableDeclaration(false, c)),
         T("reinit").e_I(parseNonemptyCommaDelimitedSeq(parseId)).M(ids => Reinit(ids)),
         T("exit").e_I(parseOptionalExitArgument()).M(optionalLabel => Exit(optionalLabel)),
         T("return").M(_ => Return),
         T("check").e_I(parseExpr).M(e => Check(e)),
         T("assume").e_I(parseExpr).M(e => Assume(e)),
         T("reach").e_I(parseExpr).M(e => Reach(e)),
         T("assert").e_I(parseExpr).M(e => Assert(e)),
         T("probe").e_I(parseExpr).M(e => Probe(e)),
         T("forall").e_I(parseIdType).I_I(c("block")).M3(Unfold3l, (name, typ, body) => AForall(name, typ, body)),
         c("block"),
         T("choose").e_I(c("block")).I_I(T("or").e_I(c("block")).Rep()).M2(MId, (s, ss) => Choose([s] + ss)),
         T("if").e_I(parseIfCont(c)),
         c("loop"),
         Atomic(parseId.I_e(Sym(":="))).I_I(parseExpr).M2(MId, (lhs, rhs) => Assign(lhs, rhs)),
         Atomic(parseId.I_e(Sym(":"))).I_I(Or([c("block"), c("loop")])).M2(MId, (lbl, stmt) => LabeledStmt(lbl, stmt)),
         Atomic(parseId.I_e(Sym("("))).I_I(parseCommaDelimitedSeq(parseCallArgument)).I_e(Sym(")")).M2(MId, (name, args) => Call(name, args))
       ])
  }

  function parseVariableDeclaration(isMutable: bool, c: StmtRecSel): B<Stmt> {
    parseIdOptionalType.M2(MId, (name: string, optionalType: Option<string>) => (name, optionalType)).
    I_I(parseOptionalAutoInvariant).M2(MId, (nameType: (string, Option<string>), autoInv: Option<Expr>) =>
      Variable(nameType.0, isMutable, nameType.1, autoInv)).
    I_I(Sym(":=").e_I(parseExpr).Option()).
    I_I(c("stmt").Rep()).M3(Unfold3l, (v, init, stmts) =>
                              VarDecl(v, init, Block(stmts)))
  }

  const parseOptionalAutoInvariant: B<Option<Expr>> :=
    T("autoinv").e_I(parseExpr).Option()

  function parseOptionalExitArgument(): B<Option<string>> {
    Lookahead(parseId.I_e(Or([Sym(":="), Sym(":"), Sym("(")]))).Then((maybe: Option<string>) =>
                                                                       if maybe.Some? then Nothing.M(_ => None) else parseId.Option()
    )
  }

  function parseIfCont(c: StmtRecSel): B<Stmt> {
    Or([
      parseCase(c).I_I(parseCase(c).Rep()).M2(MId, (caseHead, caseTail) => IfCase([caseHead] + caseTail)),
      parseExpr.I_I(c("block")).I_I(
        Or([
          T("else").e_I(
            Or([
              T("if").e_I(c("if-cont")),
              c("block")
            ])),
          Nothing.M(_ => Block([]))
        ])).M3(Unfold3l, (cond, thn, els) => If(cond, thn, els))
    ])
  }

  function parseCase(c: StmtRecSel): B<Case> {
    T("case").e_I(parseExpr).I_I(c("block")).M2(MId, (cond, body) => Case(cond, body))
  }

  function parseLoop(c: StmtRecSel): B<Stmt> {
    T("loop")
    .e_I(parseAExprSeq("invariant", c))
    .I_I(c("block"))
    .M2(MId, (invariants, body) => Loop(invariants, body))
  }

  const parseCallArgument: B<CallArgument> :=
    Or([
         T("out").e_I(parseId).M(name => CallArgument(ParameterMode.Out, IdExpr(name))),
         T("inout").e_I(parseId).M(name => CallArgument(ParameterMode.InOut, IdExpr(name))),
         parseExpr.M(e => CallArgument(ParameterMode.In, e))
       ])

  // ----- Expressions

  function parseAExprSeq(keyword: string, c: StmtRecSel): B<seq<AExpr>> {
    parseAExpr(keyword, c).Rep()
  }

  function parseAExpr(keyword: string, c: StmtRecSel): B<AExpr> {
    T(keyword).e_I(
      Or([
           c("block").M(stmt => AAssertion(stmt)),
           parseExpr.M(e => AExpr(e))
         ]))
  }

  /* Here is the expression grammar (but not formulated as an LL(1) grammar).
   *
   * Expr ::= ( ImpExpExpr "<==>" )* ImpExpExpr                     // associates to the left
   * ImpExpExpr ::= ImpliesExpr | ExpliesExpr                       // needs disambiguation after parsing one LogicalExpr
   * ImpliesExpr ::= LogicalExpr "==>" ImpliesExpr                  // associates to the right
   * ExpliesExpr ::= ( LogicalExpr "<==" )* LogicalExpr             // associates to the left
   * LogicalExpr ::= AndExpr | OrExpr                               // needs disambiguation after parsing one JunctExpr
   * AndExpr ::= ( JuctExpr "&&" )* JuctExpr                        // associates to the left
   * OrExpr ::= ( JuctExpr "||" )* JuctExpr                         // associates to the left
   * JuctExpr ::= TermExpr [ ( "==" | "!=" | "<" | "<=" | ">=" | ">" ) TermExpr ]
   * TermExpr ::= ( FactorExpr ( "+" | "-" ))* FactorExpr           // associates to the left
   * FactorExpr ::= ( UnaryExpr ( "*" | "div" | "mod" ))* UnaryExpr // associates to the left
   * UnaryExpr ::= ( "!" | "-" )* PrimaryExpr
   * PrimaryExpr ::= EndlessExpr
   *               | AtomicExpr
   * EndlessExpr ::= "if" Expr Expr "else" Expr
   *               | "var" Id ":" Type ":=" Expr ";" Expr
   *               | ( "forall" | "exists" ) (Id ":" Type)+, ( "pattern" Expr*, )* Expr
   *               | Id ":" Expr
   * AtomicExpr ::= "false" | "true"
   *              | nat
   *              | "|" literalString ":" Type "|"          // custom (uninterpreted) literals
   *              | Id
   *              | Id "(" Expr*, ")"
   *              | "(" Expr ")"
  */

  const parseExpr: B<Expr> := RecMap(exprGallery, "expr")

  function parseEquivExpr(c: ExprRecSel): B<Expr> {
    parseImpExpExpr(c).Then(e0 =>
      Sym("<==>").e_I(parseImpExpExpr(c)).Rep().M(exprs =>
        FoldLeft(e0, exprs, (a, b) => OperatorExpr(Operator.Equiv, [a, b]))
      )
    )
  }

  function parseImpExpExpr(c: ExprRecSel): B<Expr> {
    parseLogicalExpr(c).Then(e0 =>
      Or([
        Sym("==>").e_I(parseLogicalExpr(c).RepSep(Sym("==>")))
          .M(exprs => FoldRightNonempty([e0] + exprs, (a, b) => OperatorExpr(Operator.LogicalImp, [a, b]))),
        SymNotPrefix("<==", ["<==>"]).e_I(parseLogicalExpr(c).RepSep(SymNotPrefix("<==", ["<==>"])))
          .M(exprs => FoldLeft(e0, exprs, (a, b) => OperatorExpr(Operator.LogicalImp, [b, a]))),
        Nothing.M(_ => e0)
      ])
    )
  }

  function parseLogicalExpr(c: ExprRecSel): B<Expr> {
    parseJuctExpr(c).Then(e0 =>
      Or([
        Sym("&&").e_I(parseJuctExpr(c).RepSep(Sym("&&")))
          .M(exprs => FoldLeft(e0, exprs, (a, b) => OperatorExpr(Operator.LogicalAnd, [a, b]))),
        Sym("||").e_I(parseJuctExpr(c).RepSep(Sym("||")))
          .M(exprs => FoldLeft(e0, exprs, (a, b) => OperatorExpr(Operator.LogicalOr, [a, b]))),
        Nothing.M(_ => e0)
      ])
    )
  }

  function parseJuctExpr(c: ExprRecSel): B<Expr> {
    parseTermExpr(c).Then(e0 =>
      parseComparisonOperator.I_I(parseTermExpr(c)).Option().M((opt: Option<((Operator, bool), Expr)>) =>
        match opt
        case None => e0
        case Some(((op, false), e1)) => OperatorExpr(op, [e0, e1])
        case Some(((op, true), e1)) => OperatorExpr(op, [e1, e0])
    ))
  }
  const parseComparisonOperator: B<(Operator, bool)> :=
    Or([
      SymNotPrefix("==", ["==>"]).M(_ => (Operator.Eq, false)),
      Sym("!=").M(_ => (Operator.Neq, false)),
      SymNotPrefix("<=", ["<=="]).M(_ => (Operator.AtMost, false)),
      SymNotPrefix("<", ["<=="]).M(_ => (Operator.Less, false)),
      Sym(">=").M(_ => (Operator.AtMost, true)),
      Sym(">").M(_ => (Operator.Less, true))
    ])

  function parseTermExpr(c: ExprRecSel): B<Expr> {
    parseFactorExpr(c).Then(e0 =>
      Or([
        Sym("+").M(_ => Operator.Plus),
        Sym("-").M(_ => Operator.Minus)
      ]).I_I(parseFactorExpr(c)).Rep()
      .M(opExprs => FoldLeft(e0, opExprs, (a, b: (Operator, Expr)) => OperatorExpr(b.0, [a, b.1])))
    )
  }

  function parseFactorExpr(c: ExprRecSel): B<Expr> {
    parseUnaryExpr(c).Then(e0 =>
      Or([
        Sym("*").M(_ => Operator.Times),
        T("div").M(_ => Operator.Div),
        T("mod").M(_ => Operator.Mod)
      ]).I_I(parseUnaryExpr(c)).Rep()
      .M(opExprs => FoldLeft(e0, opExprs, (a, b: (Operator, Expr)) => OperatorExpr(b.0, [a, b.1])))
    )
  }

  function parseUnaryExpr(c: ExprRecSel): B<Expr> {
    Or([
      SymNotPrefix("!", ["!="]).M(_ => Operator.LogicalNot),
      Sym("-").M(_ => Operator.UnaryMinus)
    ]).Rep().I_I(parsePrimaryExpr(c)).M2(MId, (unaryOperators, expr) =>
      FoldRight(unaryOperators, (op, e) => OperatorExpr(op, [e]), expr)
    )
  }

  function parsePrimaryExpr(c: ExprRecSel): B<Expr> {
    Or([
      T("if").e_I(c("expr")).Then(guard =>
        c("expr").I_I(T("else").e_I(c("expr"))).M2(MId, (thn, els) => OperatorExpr(IfThenElse, [guard, thn, els]))
      ),
      T("val").e_I(parseIdOptionalType.Then(p => var (name: string, optionalType: Option<Types.TypeName>) := p;
        Sym(":=").e_I(c("expr")).I_I(c("expr")).M2(MId, (rhs, body) => LetExpr(name, optionalType, rhs, body)))
      ),
      Or([T("forall").M(_ => true), T("exists").M(_ => false)]).Then(universal =>
        parseNonemptyCommaDelimitedSeq(parseIdType.M2(MId, (name: string, typ: Types.TypeName) => Binding(name, typ))).Then(bindings =>
          parsePattern(c).Rep().Then(patterns =>
            c("expr").M(body => QuantifierExpr(universal, bindings, patterns, body))
          )
        )
      ),
      T("lift").e_I(parseClosure(c)),
      parseAtomicExpr(c)
    ])
  }

  function parseClosure(c: ExprRecSel): B<Expr> {
    parseNonemptyCommaDelimitedSeq(parseClosureBinding(c)).Then(bindings =>
      T("into").e_I(parseId).Then(resultVar =>
        Sym(":").e_I(parseType).Then(resultType =>
          T("by").e_I(Sym("{")).e_I(parseCommaDelimitedSeq(parseClosureProperty(c))).I_e(Sym("}")).M(properties =>
            ClosureExpr(bindings, resultVar, resultType, properties)
          )
        )
      )
    )
  }

  function parseClosureBinding(c: ExprRecSel): B<ClosureBinding> {
    parseId.Then(name =>
      parseParenthesized(parseCommaDelimitedSeq(parseIdType.M2(MId, (n: string, t: Types.TypeName) => Binding(n, t)))).Option().Then((maybeParams: Option<seq<Binding>>) =>
        Sym(":=").e_I(c("expr")).M(rhs =>
          var params: seq<Binding> := match maybeParams case Some(p) => p case None => [];
          ClosureBinding(name, params, rhs)
        )
      )
    )
  }

  function parseClosureProperty(c: ExprRecSel): B<ClosureProperty> {
    parseClosureTrigger(c).Rep().Then(triggers =>
      c("expr").M(body =>
        ClosureProperty(triggers, body)
      )
    )
  }

  function parseClosureTrigger(c: ExprRecSel): B<Pattern> {
    T("trigger").e_I(parseNonemptyCommaDelimitedSeq(c("expr"))).M(exprs => Pattern(exprs))
  }

  function parsePattern(c: ExprRecSel): B<Pattern> {
    T("pattern").e_I(parseNonemptyCommaDelimitedSeq(c("expr"))).M(exprs => Pattern(exprs))
  }

  function parseAtomicExpr(c: ExprRecSel): B<Expr> {
    Or([
      T("false").M(_ => BLiteral(false)),
      T("true").M(_ => BLiteral(true)),
      Nat.I_e(W).M(n => ILiteral(n)),
      Sym("|").e_I(parseCustomLiteral).I_e(Sym(":")).I_I(parseType).I_e(Sym("|")).M2(MId, (lit, typ) => CustomLiteral(lit, typ)),
      T("old").e_I(parseId).M(name => IdExpr(name, true)),
      parseId.Then(name =>
        Or([
          Sym("(").e_I(parseCommaDelimitedSeq(c("expr"))).I_e(Sym(")"))
            .M(args => FunctionCallExpr(name, args)),
          Sym(":").e_I(c("expr")).M(e => LabeledExpr(name, e)),
          Nothing.M(_ => IdExpr(name, false))
        ])),
      Sym("(").e_I(c("expr")).I_e(Sym(")"))
    ])
  }
}
