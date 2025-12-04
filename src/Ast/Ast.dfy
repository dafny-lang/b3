module Ast {
  import opened Std.Wrappers
  import opened Basics
  import Types
  import Raw = RawAst
  import opened Values
  import opened DeclarationMarkers
  import PrintUtil

  export
    reveals NamedDecl, NamedDecl.Distinct, TypeDecl, Type
    provides NamedDecl.Name, Type.ToString
    reveals Program, Type, Variable, Procedure, Label, PParameter, LocalVariable
    reveals Expr, Operator, ParameterMode, AExpr, Location, Stmt, CallArgument
    reveals AutoInvVariable
    reveals Program.WellFormed, Procedure.WellFormed, PParameter.WellFormed, AExpr.WellFormed, Stmt.WellFormed, Expr.WellFormed, CallArgument.WellFormed
    reveals CallArgument.CorrespondingMode
    provides Procedure.Parameters, Procedure.Pre, Procedure.Post, Procedure.Body
    reveals Procedure.SignatureCorrespondence, Procedure.WellFormedHeader
    reveals Function, FParameter, FunctionDefinition
    reveals Function.SignatureCorrespondence, Function.SignatureWellFormed, Function.WellFormed, Function.WellFormedAsTagger, FParameter.WellFormed, FunctionDefinition.WellFormed
    provides Function.Parameters, Function.ResultType, Function.Tag, Function.Definition, Function.ExplainedBy, FParameter.injective
    reveals Axiom, Axiom.WellFormed
    provides Axiom.Explains, Axiom.Expr
    provides Variable.name, Variable.typ
    provides Variable.IsMutable, LocalVariable.IsMutable, PParameter.IsMutable, FParameter.IsMutable
    provides AutoInvVariable.maybeAutoInv
    provides PParameter.mode, PParameter.oldInOut
    provides Label.Name
    provides Location.description
    reveals Stmt.IsPredicateStmt
    reveals Expr.ExprType, Expr.HasType
    provides Expr.ToString
    provides Expr.FreeVariables, Expr.FreeVariablesInList
    provides Expr.CreateTrue, Expr.CreateFalse, Expr.CreateNegation, Expr.CreateLet, Expr.CreateForall
    provides Expr.CreateAnd, Expr.CreateBigAnd, Expr.CreateOr, Expr.CreateBigOr
    reveals Pattern, Pattern.WellFormed
    reveals ClosureBinding, ClosureBinding.WellFormed
    reveals ClosureProperty, ClosureProperty.WellFormed
    provides Raw, Types, Wrappers, DeclarationMarkers, PrintUtil

  trait NamedDecl extends object {
    const Name: string

    static predicate Distinct(decls: seq<NamedDecl>) {
      forall i, j :: 0 <= i < j < |decls| ==> decls[i].Name != decls[j].Name
    }
  }

  class TypeDecl extends NamedDecl {
    constructor (name: string)
      ensures Name == name
    {
      Name := name;
    }
  }

  datatype Type =
    | BoolType
    | IntType
    | TagType
    | UserType(decl: TypeDecl)
  {
    function ToString(): string {
      match this
      case BoolType => Types.BoolTypeName
      case IntType => Types.IntTypeName
      case TagType => Types.TagTypeName
      case UserType(decl) => decl.Name
    }
  }

  datatype Program = Program(types: seq<TypeDecl>, functions: seq<Function>, axioms: seq<Axiom>, procedures: seq<Procedure>)
  {
    predicate WellFormed()
      reads procedures, functions
    {
      // type declarations have distinct names
      && NamedDecl.Distinct(types)

      // function declarations have distinct names
      && NamedDecl.Distinct(functions)
      // function are well-formed
      && (forall func <- functions :: func.WellFormed())

      // axioms are well-formed
      && (forall axiom <- axioms :: axiom.WellFormed())

      // procedure declarations have distinct names
      && NamedDecl.Distinct(procedures)
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

  trait AutoInvVariable extends Variable {
    var maybeAutoInv: Option<Expr>
  }

  class Procedure extends NamedDecl {
    const Parameters: seq<PParameter>
    const Pre: seq<AExpr>
    const Post: seq<AExpr>
    var Body: Option<Stmt>

    constructor (name: string, parameters: seq<PParameter>, pre: seq<AExpr>, post: seq<AExpr>)
      ensures Name == name && Parameters == parameters
      ensures Pre == pre && Post == post && Body == None
    {
      Name, Parameters := name, parameters;
      Pre, Post := pre, post;
      Body := None; // this is set after construction
    }

    ghost predicate SignatureCorrespondence(proc: Raw.Procedure) {
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

  class PParameter extends AutoInvVariable {
    const mode: ParameterMode
    const oldInOut: Option<Variable>

    constructor (name: string, mode: ParameterMode, typ: Type, oldInOut: Option<Variable>)
      ensures this.name == name && this.mode == mode && this.typ == typ && this.oldInOut == oldInOut && this.maybeAutoInv == None
    {
      this.name, this.mode, this.typ, this.maybeAutoInv := name, mode, typ, None;
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

  class Function extends NamedDecl, DeclarationMarker {
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

    predicate SignatureCorrespondence(func: Raw.Function) {
      && Name == func.name
      && |Parameters| == |func.parameters|
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].name == func.parameters[i].name)
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].injective == func.parameters[i].injective)
      && (if func.tag == None then Tag == None else Tag.Some? && Tag.value.Name == func.tag.value)
    }

    predicate SignatureWellFormed() {
      && (forall i :: 0 <= i < |Parameters| ==> Parameters[i].WellFormed())
      && (forall i, j :: 0 <= i < j < |Parameters| ==> Parameters[i].name != Parameters[j].name)
      && (Tag.Some? ==> var tagger := Tag.value; |tagger.Parameters| == 1 && tagger.Parameters[0].typ == ResultType)
    }

    predicate WellFormed()
      reads this
    {
      && SignatureWellFormed()
      && (Definition == None || Definition.value.WellFormed())
    }

    predicate WellFormedAsTagger()
      reads this
    {
      && WellFormed()
      && Tag == None
      && |Parameters| == 1
      && !Parameters[0].injective
      && ResultType == TagType
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
      Raw.LegalVariableName(name)
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

  class LocalVariable extends AutoInvVariable {
    const isMutable: bool
    constructor (name: string, isMutable: bool, typ: Type)
      ensures this.name == name && this.maybeAutoInv == None
    {
      this.name, this.isMutable, this.typ, this.maybeAutoInv := name, isMutable, typ, None;
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

  class Location {
    const description: string

    constructor (description: string) {
      this.description := description;
    }
  }

  datatype Stmt =
    | VarDecl(v: AutoInvVariable, initial: Option<Expr>, body: Stmt)
    | Assign(lhs: Variable, rhs: Expr)
    | Reinit(vars: seq<Variable>)
    | Block(stmts: seq<Stmt>)
    | Call(proc: Procedure, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr, location: Location)
    | Assume(cond: Expr)
    | Reach(cond: Expr, location: Location)
    | Assert(cond: Expr, location: Location)
    | AForall(bv: Variable, body: Stmt)
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
      case Reinit(vars) =>
        forall i, j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
      case Block(stmts) => forall stmt <- stmts :: stmt.WellFormed()
      case Call(proc, args) =>
        && |args| == |proc.Parameters|
        && (forall i :: 0 <= i < |args| ==> args[i].CorrespondingMode() == proc.Parameters[i].mode)
        && (forall arg <- args :: arg.WellFormed())
      case Check(cond, _) => cond.WellFormed()
      case Assume(cond) => cond.WellFormed()
      case Reach(cond, _) => cond.WellFormed()
      case Assert(cond, _) => cond.WellFormed()
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
      Check? || Assume? || Reach? || Assert?
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
    | AExpr(e: Expr, location: Location)
    | AAssertion(s: Stmt)
  {
    predicate WellFormed() {
      match this
      case AExpr(e, _) => e.WellFormed()
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
    | ClosureExpr(closureBindings: seq<ClosureBinding>, resultVar: string, resultType: Type, properties: seq<ClosureProperty>)
  {
    function ExprType(): Type {
      match this
      case BLiteral(_) => BoolType
      case ILiteral(_) => IntType
      case CustomLiteral(_, typ) => typ
      case IdExpr(v) => v.typ
      case OperatorExpr(op, args) =>
        match op {
          case IfThenElse =>
            if op.ArgumentCount() == |args| then args[1].ExprType() else BoolType // TODO: Rather than an `else` branch, use a WellFormed precondition
          case Equiv | LogicalImp | LogicalAnd | LogicalOr | LogicalNot =>
            BoolType
          case Eq | Neq | Less | AtMost =>
            BoolType
          case Plus | Minus | Times | Div | Mod | UnaryMinus =>
            IntType
        }
      case FunctionCallExpr(func, args) => func.ResultType
      case LabeledExpr(_, body) => body.ExprType()
      case LetExpr(_, _, body) => body.ExprType()
      case QuantifierExpr(_, _, _, _) => BoolType
      case ClosureExpr(_, _, resultType, _) => resultType
    }

    predicate HasType(typ: Type) {
      ExprType() == typ
    }

    predicate WellFormed() {
      match this
      case BLiteral(_) => true
      case ILiteral(_) => true
      case CustomLiteral(_, typ) => typ != BoolType && typ != IntType
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
      case ClosureExpr(closureBindings, _, _, properties) =>
        && (forall b <- closureBindings :: b.WellFormed())
        && (forall p <- properties :: p.WellFormed())
    }

    function ToString(context: PrintUtil.BindingPower := PrintUtil.BindingPower.Init): string {
      match this
      case BLiteral(value) => if value then "true" else "false"
      case ILiteral(value) => Int2String(value)
      case CustomLiteral(s, typ) => PrintUtil.CustomLiteralToString(s, typ.ToString())
      case IdExpr(v) => v.name
      case OperatorExpr(op, args) =>
        var opStrength := op.BindingStrength();
        PrintUtil.ParenthesisWrap(opStrength, context,
          if op == Operator.IfThenElse && op.ArgumentCount() == |args| then
            "if " + args[0].ToString() +
            " " + args[1].ToString() +
            " else " + args[2].ToString(opStrength.SubexpressionPower(PrintUtil.Right, context))
          else if op.ArgumentCount() == 1 == |args| then
            op.ToString() + args[0].ToString(opStrength.SubexpressionPower(PrintUtil.Right, context))
          else if op.ArgumentCount() == 2 == |args| then
            args[0].ToString(opStrength.SubexpressionPower(PrintUtil.Left, context)) +
            " " + op.ToString() + " " +
            args[1].ToString(opStrength.SubexpressionPower(PrintUtil.Right, context))
          else
            op.ToString() + "(" + ListToString(args) + ")")
      case FunctionCallExpr(func, args) =>
        func.Name + "(" + ListToString(args) + ")"
      case LabeledExpr(lbl, expr) =>
        var opStrength := PrintUtil.BindingPower.EndlessOperator;
        PrintUtil.ParenthesisWrap(opStrength, context,
          lbl.Name + ": " + expr.ToString(opStrength.SubexpressionPower(PrintUtil.Right, context))
        )
      case LetExpr(v, rhs, body) =>
        var opStrength := PrintUtil.BindingPower.EndlessOperator;
        PrintUtil.ParenthesisWrap(opStrength, context,
          v.DeclToString() + " := " + rhs.ToString() + " " + body.ToString(opStrength.SubexpressionPower(PrintUtil.Right, context))
        )
      case QuantifierExpr(univ, vv, patterns, body) =>
        var opStrength := PrintUtil.BindingPower.EndlessOperator;
        PrintUtil.ParenthesisWrap(opStrength, context,
          var opStrength := PrintUtil.BindingPower.EndlessOperator;
          (if univ then "forall " else "exists ") +
          DeclsToString(vv) +
          Pattern.ListToString(patterns) + " " + body.ToString(opStrength.SubexpressionPower(PrintUtil.Right, context))
        )
      case ClosureExpr(closureBindings, resultVar, resultType, properties) =>
        "lift" + ClosureBindingsToString(closureBindings) + " into " + resultVar + ": " + resultType.ToString() + " by { " + ClosurePropertiesToString(properties) + " }"
    }

    static function ClosureBindingsToString(bindings: seq<ClosureBinding>): string {
      if |bindings| == 0 then ""
      else if |bindings| == 1 then " " + ClosureBindingToString(bindings[0])
      else " " + ClosureBindingToString(bindings[0]) + ", " + ClosureBindingsToString(bindings[1..])
    }

    static function ClosureBindingToString(binding: ClosureBinding): string {
      binding.name + 
      (if |binding.params| == 0 then "" else "(" + ParamsToString(binding.params) + ")") +
      " := " + binding.rhs.ToString()
    }

    static function ParamsToString(params: seq<(string, Type)>): string {
      Comma(SeqMap(params, (p: (string, Type)) => p.0 + ": " + p.1.ToString()), ", ")
    }

    static function ClosurePropertiesToString(properties: seq<ClosureProperty>): string {
      var ss := SeqMap(properties, prop requires prop in properties => ClosurePropertyToString(prop));
      Comma(ss, ", ")
    }

    static function ClosurePropertyToString(prop: ClosureProperty): string {
      Pattern.ListToString(prop.triggers) + " " + prop.body.ToString()
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

    // Returns the free variables, except for variables occurring only in patterns
    function FreeVariables(): set<Variable> {
      match this
      case BLiteral(_) => {}
      case ILiteral(_) => {}
      case CustomLiteral(_, _) => {}
      case IdExpr(v) => {v}
      case OperatorExpr(_, args) => FreeVariablesInList(args)
      case FunctionCallExpr(_, args) => FreeVariablesInList(args)
      case LabeledExpr(_, body) => body.FreeVariables()
      case LetExpr(_, rhs, body) => rhs.FreeVariables() + body.FreeVariables()
      case QuantifierExpr(_, vv, _, body) =>
        // don't look in patterns
        body.FreeVariables() - set v <- vv :: v
      case ClosureExpr(closureBindings, _, _, properties) =>
        // Free variables from bindings and properties
        var bindingVars := set b <- closureBindings, v <- b.rhs.FreeVariables() :: v;
        var propertyVars := set p <- properties, v <- p.body.FreeVariables() :: v;
        bindingVars + propertyVars
    }

    static function FreeVariablesInList(exprs: seq<Expr>): set<Variable> {
      if exprs == [] then
        {}
      else
        exprs[0].FreeVariables() + FreeVariablesInList(exprs[1..])
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

  datatype ClosureBinding = ClosureBinding(name: string, params: seq<(string, Type)>, rhs: Expr)
  {
    predicate WellFormed() {
      rhs.WellFormed()
    }
  }

  datatype ClosureProperty = ClosureProperty(triggers: seq<Pattern>, body: Expr)
  {
    predicate WellFormed() {
      && (forall tr <- triggers :: tr.WellFormed())
      && body.WellFormed()
    }
  }
}
