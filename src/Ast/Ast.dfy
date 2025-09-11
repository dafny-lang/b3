module Ast {
  import opened Std.Wrappers
  import opened Basics
  import Types
  import Raw = RawAst
  import opened Values
  import opened DeclarationMarkers

  export
    reveals Program, Type, Variable, Procedure, Label, Parameter, LocalVariable
    reveals Expr, Operator, ParameterMode, AExpr, Stmt, CallArgument
    reveals Program.WellFormed, Procedure.WellFormed, Parameter.WellFormed, AExpr.WellFormed, Stmt.WellFormed, Expr.WellFormed, CallArgument.WellFormed
    reveals CallArgument.CorrespondingMode
    provides Procedure.Name, Procedure.Parameters, Procedure.Pre, Procedure.Post, Procedure.Body
    reveals Procedure.SignatureWellFormed, Procedure.WellFormedHeader
    reveals Function, FParameter, FunctionDefinition
    provides Function.Name, Function.Parameters, Function.ResultType, Function.Tag, Function.Definition, Function.ExplainedBy, FParameter.injective
    reveals Function.SignatureWellFormed, Function.WellFormed, Function.WellFormedAsTagger, FParameter.WellFormed, FunctionDefinition.WellFormed
    reveals Axiom, Axiom.WellFormed
    provides Axiom.Explains, Axiom.Expr
    provides Variable.name, Variable.typ
    provides Variable.IsMutable, LocalVariable.IsMutable, Parameter.IsMutable, FParameter.IsMutable
    provides Parameter.mode, Parameter.oldInOut
    provides Label.Name
    reveals Stmt.IsPredicateStmt
    reveals Expr.ExprType, Expr.HasType
    provides Expr.ToString
    provides Expr.CreateTrue, Expr.CreateFalse, Expr.CreateNegation, Expr.CreateLet, Expr.CreateForall
    provides Expr.CreateAnd, Expr.CreateBigAnd, Expr.CreateOr, Expr.CreateBigOr
    reveals Pattern, Pattern.WellFormed
    provides CustomLiteralToString
    provides Raw, Types, Wrappers, DeclarationMarkers

  type Type = Types.Type

  datatype Program = Program(types: seq<Types.TypeDecl>, functions: seq<Function>, axioms: seq<Axiom>, procedures: seq<Procedure>)
  {
    predicate WellFormed()
      reads procedures, functions
    {
      // type declarations have distinct names
      && (forall typ0 <- types, typ1 <- types :: typ0.Name == typ1.Name ==> typ0 == typ1)

      // function declarations have distinct names
      && (forall func0 <- functions, func1 <- functions :: func0.Name == func1.Name ==> func0 == func1)
      // function are well-formed
      && (forall func <- functions :: func.WellFormed())

      // axioms are well-formed
      && (forall axiom <- axioms :: axiom.WellFormed())

      // procedure declarations have distinct names
      && (forall proc0 <- procedures, proc1 <- procedures :: proc0.Name == proc1.Name ==> proc0 == proc1)
      // procedures are well-formed
      && (forall proc <- procedures :: proc.WellFormed())
    }
  }

  trait Variable extends object {
    const name: string
    const typ: Type

    predicate IsMutable()

    function DeclToString(): string
  }

  class Procedure {
    const Name: string
    const Parameters: seq<Parameter>
    const Pre: seq<AExpr>
    const Post: seq<AExpr>
    var Body: Option<Stmt>

    constructor (name: string, parameters: seq<Parameter>, pre: seq<AExpr>, post: seq<AExpr>)
      ensures Name == name && Parameters == parameters
      ensures Pre == pre && Post == post && Body == None
    {
      Name, Parameters := name, parameters;
      Pre, Post := pre, post;
      Body := None; // this is set after construction
    }

    ghost predicate SignatureWellFormed(proc: Raw.Procedure) {
      && Name == proc.name
      && (forall formal <- Parameters :: Raw.LegalVariableName(formal.name))
      && (forall i, j :: 0 <= i < j < |Parameters| ==> Parameters[i].name != Parameters[j].name)
      && |Parameters| == |proc.parameters|
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].name == proc.parameters[i].name)
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].mode == proc.parameters[i].mode)
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].WellFormed())
    }

    predicate WellFormedHeader() {
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].WellFormed())
      && (forall i, j :: 0 <= i < j < |Parameters| ==> Parameters[i].name != Parameters[j].name)
      && (forall pre <- Pre :: pre.WellFormed())
      && (forall post <- Post :: post.WellFormed())
    }

    predicate WellFormed()
      reads this
    {
      && WellFormedHeader()
      && (Body.Some? ==> Body.value.WellFormed())
      // TODO: make sure free variables of Pre/Post/Body are the expected ones
    }
  }

  class Parameter extends Variable {
    const mode: ParameterMode
    const oldInOut: Option<Variable>

    constructor (name: string, mode: ParameterMode, typ: Type, oldInOut: Option<Variable>)
      ensures this.name == name && this.mode == mode && this.typ == typ && this.oldInOut == oldInOut
    {
      this.name, this.mode, this.typ := name, mode, typ;
      this.oldInOut := oldInOut;
    }

    predicate WellFormed() {
      oldInOut.Some? <==> mode == ParameterMode.InOut
    }

    predicate IsMutable() {
      mode != ParameterMode.In
    }

    function DeclToString(): string {
      name + ": " + typ.ToString()
    }
  }

  type ParameterMode = Raw.ParameterMode

  class Function extends DeclarationMarker {
    const Name: string
    const Parameters: seq<FParameter>
    const ResultType: Type
    const Tag: Option<Function>
    var Definition: Option<FunctionDefinition>
    var ExplainedBy: seq<Axiom>

    constructor (name: string, parameters: seq<FParameter>, resultType: Type, maybeTag: Option<Function>)
      ensures Name == name && Parameters == parameters && ResultType == resultType && Tag == maybeTag && Definition == None
      ensures ExplainedBy == []
    {
      Name := name;
      Parameters := parameters;
      ResultType := resultType;
      Tag := maybeTag;
      Definition := None;
      ExplainedBy := [];
    }

    ghost predicate SignatureWellFormed(func: Raw.Function) {
      && Name == func.name
      && (forall formal <- Parameters :: Raw.LegalVariableName(formal.name))
      && (forall i, j :: 0 <= i < j < |Parameters| ==> Parameters[i].name != Parameters[j].name)
      && |Parameters| == |func.parameters|
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].name == func.parameters[i].name)
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].injective == func.parameters[i].injective)
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].WellFormed())
      && (if func.tag == None then Tag == None else Tag.Some? && Tag.value.Name == func.tag.value)
      && (Tag.Some? ==> var tagger := Tag.value; |tagger.Parameters| == 1 && tagger.Parameters[0].typ == ResultType)
    }

    predicate WellFormed()
      reads this
    {
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].WellFormed())
      && (forall i, j :: 0 <= i < j < |Parameters| ==> Parameters[i].name != Parameters[j].name)
      && (Definition == None || Definition.value.WellFormed())
      && (Tag.Some? ==> var tagger := Tag.value; |tagger.Parameters| == 1 && tagger.Parameters[0].typ == ResultType)
    }

    predicate WellFormedAsTagger()
      reads this
    {
      && WellFormed()
      && |Parameters| == 1
      && ResultType == Types.TagType
    }
  }

  datatype FunctionDefinition = FunctionDefinition(when: seq<Expr>, body: Expr)
  {
    predicate WellFormed() {
      && (forall e <- when :: e.WellFormed())
      && (body.WellFormed())
      // TODO: make sure free/bound variables of when/body are the expected ones
    }
  }

  class FParameter extends Variable {
    const injective: bool

    constructor (name: string, injective: bool, typ: Type)
      ensures this.name == name && this.injective == injective && this.typ == typ
    {
      this.name, this.injective, this.typ := name, injective, typ;
    }

    predicate WellFormed() {
      true
    }

    predicate IsMutable() {
      false
    }

    function DeclToString(): string {
      (if injective then "injective " else "") + name + ": " + typ.ToString()
    }
  }

  class Axiom extends DeclarationMarker {
    const Explains: seq<Function>
    const Expr: Expr

    constructor (explains: seq<Function>, expr: Expr)
      ensures Explains == explains && Expr == expr
    {
      this.Explains := explains;
      this.Expr := expr;
    }

    predicate WellFormed() {
      Expr.WellFormed()
    }
  }

  class LocalVariable extends Variable {
    const isMutable: bool
    constructor (name: string, isMutable: bool, typ: Type)
      ensures this.name == name
    {
      this.name, this.isMutable, this.typ := name, isMutable, typ;
    }

    predicate IsMutable() {
      isMutable
    }

    function DeclToString(): string {
      (if isMutable then "var " else "val ") + name + ": " + typ.ToString()
    }
  }

  class Label {
    const Name: string

    constructor (name: string)
      ensures Name == name
    {
      Name := name;
    }
  }

  datatype Stmt =
    | VarDecl(v: Variable, initial: Option<Expr>, body: Stmt)
    | Assign(lhs: Variable, rhs: Expr)
    | Block(stmts: seq<Stmt>)
    | Call(proc: Procedure, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr)
    | Assume(cond: Expr)
    | Assert(cond: Expr)
    | AForall(v: Variable, body: Stmt)
    // Control flow
    | Choose(branches: seq<Stmt>)
    | Loop(invariants: seq<AExpr>, body: Stmt)
    | LabeledStmt(lbl: Label, body: Stmt)
    | Exit(lbl: Label)
    // Error reporting
    | Probe(e: Expr)
  {
    predicate WellFormed() {
      match this
      case VarDecl(_, initial, body) => 
        && (initial.Some? ==> initial.value.WellFormed())
        && body.WellFormed()
      case Assign(_, rhs) => rhs.WellFormed()
      case Block(stmts) => forall stmt <- stmts :: stmt.WellFormed()
      case Call(proc, args) =>
        && |args| == |proc.Parameters|
        && (forall i :: 0 <= i < |args| ==> args[i].CorrespondingMode() == proc.Parameters[i].mode)
        && (forall arg <- args :: arg.WellFormed())
      case Check(cond) => cond.WellFormed()
      case Assume(cond) => cond.WellFormed()
      case Assert(cond) => cond.WellFormed()
      case AForall(_, body) => body.WellFormed()
      case Choose(branches) =>
        forall branch <- branches :: branch.WellFormed()
      case Loop(invariants, body) =>
        && (forall inv <- invariants :: inv.WellFormed())
        && body.WellFormed()
      case LabeledStmt(lbl, body) => body.WellFormed()
      case Exit(_) => true
      case Probe(e) => e.WellFormed()
    }
    
    predicate IsPredicateStmt() {
      Check? || Assume? || Assert?
    }
  }

  datatype Case = Case(cond: Expr, body: Stmt)

  datatype CallArgument =
    | InArgument(e: Expr)
    | OutgoingArgument(isInOut: bool, v: Variable)
  {
    function CorrespondingMode(): ParameterMode {
      match this
      case InArgument(_) => ParameterMode.In
      case OutgoingArgument(isInOut, _) => if isInOut then ParameterMode.InOut else ParameterMode.Out
    }

    predicate WellFormed() {
      match this
      case InArgument(e) => e.WellFormed()
      case OutgoingArgument(_, _) => true
    }
  }

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)
  {
    predicate WellFormed() {
      match this
      case AExpr(e) => e.WellFormed()
      case AAssertion(s) => s.WellFormed()
    }
  }

  type Operator = Raw.Operator

  datatype Expr =
    | BLiteral(bvalue: bool)
    | ILiteral(ivalue: int)
    | CustomLiteral(s: string, typ: Type)
    | IdExpr(v: Variable)
    | OperatorExpr(op: Operator, args: seq<Expr>)
    | FunctionCallExpr(func: Function, args: seq<Expr>)
    | LabeledExpr(lbl: Label, body: Expr)
    | LetExpr(v: Variable, rhs: Expr, body: Expr)
    | QuantifierExpr(univ: bool, vv: seq<Variable>, patterns: seq<Pattern>, body: Expr)
  {
    function ExprType(): Type {
      match this
      case BLiteral(_) => Types.BoolType
      case ILiteral(_) => Types.IntType
      case CustomLiteral(_, typ) => typ
      case IdExpr(v) => v.typ
      case OperatorExpr(op, args) =>
        match op {
          case IfThenElse =>
            if op.ArgumentCount() == |args| then args[1].ExprType() else Types.BoolType // TODO: Rather than an `else` branch, use a WellFormed precondition
          case Equiv | LogicalImp | LogicalAnd | LogicalOr | LogicalNot =>
            Types.BoolType
          case Eq | Neq | Less | AtMost =>
            Types.BoolType
          case Plus | Minus | Times | Div | Mod | UnaryMinus =>
            Types.IntType
        }
      case FunctionCallExpr(func, args) => func.ResultType
      case LabeledExpr(_, body) => body.ExprType()
      case LetExpr(_, _, body) => body.ExprType()
      case QuantifierExpr(_, _, _, _) => Types.BoolType
    }

    predicate HasType(typ: Type) {
      ExprType() == typ
    }

    predicate WellFormed() {
      match this
      case BLiteral(_) => true
      case ILiteral(_) => true
      case CustomLiteral(_, typ) => typ != Types.BoolType && typ != Types.IntType
      case IdExpr(_) => true
      case OperatorExpr(op, args) =>
        && |args| == op.ArgumentCount()
        && forall arg <- args :: arg.WellFormed()
      case FunctionCallExpr(func, args) =>
        && |args| == |func.Parameters|
        && forall arg <- args :: arg.WellFormed()
      case LabeledExpr(_, body) =>
        body.WellFormed()
      case LetExpr(_, rhs, body) =>
        rhs.WellFormed() && body.WellFormed()
      case QuantifierExpr(_, vv, patterns, body) =>
        // SOON: && (forall i, j :: 0 <= i < j < |vv| ==> vv[i].name != vv[j].name)
        && (forall tr <- patterns :: tr.WellFormed())
        && body.WellFormed()
    }

    function ToString(contextStrength: nat := 0): string {
      match this
      case BLiteral(value) => if value then "true" else "false"
      case ILiteral(value) => Int2String(value)
      case CustomLiteral(s, typ) => CustomLiteralToString(s, typ.ToString())
      case IdExpr(v) => v.name
      case OperatorExpr(op, args) =>
        var opStrength := op.BindingStrength();
        ParenthesisWrap(opStrength <= contextStrength,
          if op == Operator.IfThenElse && op.ArgumentCount() == |args| then
            "if " + args[0].ToString() + " then " + args[1].ToString() + " els " + args[2].ToString(opStrength)
          else if op.ArgumentCount() == 1 == |args| then
            op.ToString() + args[0].ToString(opStrength)
          else if op.ArgumentCount() == 2 == |args| then
            args[0].ToString(opStrength) + " " + op.ToString() + " " + args[1].ToString(opStrength)
          else
            op.ToString() + ParenthesisWrap(true, ListToString(args)))
      case FunctionCallExpr(func, args) =>
        func.Name + ParenthesisWrap(true, ListToString(args))
      case LabeledExpr(lbl, expr) =>
        var opStrength := Operator.EndlessOperatorBindingStrength;
        ParenthesisWrap(opStrength <= contextStrength, lbl.Name + ": " + expr.ToString(opStrength))
      case LetExpr(v, rhs, body) =>
        var opStrength := Operator.EndlessOperatorBindingStrength;
        ParenthesisWrap(opStrength <= contextStrength,
          v.DeclToString() + " := " + rhs.ToString() + " " + body.ToString(opStrength)
        )
      case QuantifierExpr(univ, vv, patterns, body) =>
        var opStrength := Operator.EndlessOperatorBindingStrength;
        ParenthesisWrap(opStrength <= contextStrength,
          var opStrength := Operator.EndlessOperatorBindingStrength;
          (if univ then "forall " else "exists ") +
          DeclsToString(vv) +
          Pattern.ListToString(patterns) + " " + body.ToString(opStrength)
        )
    }

    static function DeclsToString(vv: seq<Variable>): string {
      Comma(SeqMap(vv, (v: Variable) => v.DeclToString()), ", ")
    }

    static function ListToString(exprs: seq<Expr>): string {
      if |exprs| == 0 then
        ""
      else if |exprs| == 1 then
        exprs[0].ToString()
      else
        exprs[0].ToString() + ", " + ListToString(exprs[1..])
    }

    static function ParenthesisWrap(useParentheses: bool, s: string): string {
      if useParentheses then
        "(" + s + ")"
      else
        s
    }

    static function CreateTrue(): (r: Expr)
      ensures r.WellFormed()
    { BLiteral(true) }

    static function CreateFalse(): (r: Expr)
      ensures r.WellFormed()
    { BLiteral(false) }

    static function CreateNegation(e: Expr): (r: Expr)
      requires e.WellFormed()
      ensures r.WellFormed()
    { OperatorExpr(Operator.LogicalNot, [e]) }

    static function CreateLet(v: Variable, rhs: Expr, body: Expr): (r: Expr)
      requires rhs.WellFormed() && body.WellFormed()
      ensures r.WellFormed()
    { LetExpr(v, rhs, body) }

    static function CreateForall(v: Variable, body: Expr): (r: Expr)
      requires body.WellFormed()
      ensures r.WellFormed()
    { QuantifierExpr(true, [v], [], body) }

    static function CreateAnd(e0: Expr, e1: Expr): (r: Expr)
      requires e0.WellFormed() && e1.WellFormed()
      ensures r.WellFormed()
    {
      OperatorExpr(Operator.LogicalAnd, [e0, e1])
    }

    static function CreateOr(e0: Expr, e1: Expr): (r: Expr)
      requires e0.WellFormed() && e1.WellFormed()
      ensures r.WellFormed()
    {
      OperatorExpr(Operator.LogicalOr, [e0, e1])
    }

    static function CreateBigAnd(exprs: seq<Expr>): (r: Expr)
      requires forall e <- exprs :: e.WellFormed()
      ensures r.WellFormed()
    {
      if exprs == [] then CreateTrue() else CreateAnd(exprs[0], CreateBigAnd(exprs[1..]))
    }

    static function CreateBigOr(exprs: seq<Expr>): (r: Expr)
      requires forall e <- exprs :: e.WellFormed()
      ensures r.WellFormed()
    {
      if exprs == [] then CreateFalse() else CreateOr(exprs[0], CreateBigOr(exprs[1..]))
    }
  }

  datatype Pattern = Pattern(exprs: seq<Expr>)
  {
    predicate WellFormed() {
      forall e <- exprs :: e.WellFormed()
    }

    static function ListToString(patterns: seq<Pattern>): string {
      if patterns == [] then
        ""
      else
        " pattern " + Expr.ListToString(patterns[0].exprs) + ListToString(patterns[1..])
    }
  }

  function CustomLiteralToString(s: string, typeName: string): string {
    "|" + s + ": " + typeName + "|"
  }
}
