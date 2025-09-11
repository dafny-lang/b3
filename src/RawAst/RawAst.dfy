module RawAst {
  import opened Std.Wrappers
  import opened Basics
  import opened Types

  // Top-level program

  // A raw program reflects program that has been parsed.
  datatype Program = Program(types: seq<TypeName>, taggers: seq<Tagger>, functions: seq<Function>, axioms: seq<Axiom>, procedures: seq<Procedure>)
  {
    // A raw program is well-formed when its identifiers resolve to declarations and some basic
    // properties hold:
    //    + no scope declares duplicate names
    //    + every name (of a type, procedure, function, variable) resolves to a declaration
    //    + the arity of each call (of a procedure or function) matches that of the callee
    //    + parameter modes of formal and actual call arguments match
    // Well-formedness of a raw program does NOT imply things like
    //    - type correctness
    //    - no duplication of actual out-going parameters
    //    - assignments only to mutable variables
    //    - additional semantic rules
    predicate WellFormed() {
      // user-defined types do not use the names of built-in types
      && (forall typ <- types :: typ !in BuiltInTypes)
      // user-defined types have distinct names
      && (forall i, j :: 0 <= i < j < |types| ==> types[i] != types[j])
      // procedures have distinct names
      && (forall i, j :: 0 <= i < j < |procedures| ==> procedures[i].name != procedures[j].name)
      // procedure declarations are well-formed
      && (forall proc <- procedures :: proc.WellFormed(this))
    }

    method FindProcedure(name: string) returns (r: Option<Procedure>) {
      if proc :| proc in procedures && proc.name == name {
        return Some(proc);
      }
      return None;
    }

    predicate IsType(typ: TypeName) {
      typ in BuiltInTypes || typ in types
    }
  }

  // Taggers

  datatype Tagger = Tagger(name: string, typ: TypeName)
  {
    predicate WellFormed(b3: Program) {
      true
    }
  }

  // Functions

  datatype Function = Function(name: string, parameters: seq<FParameter>, resultType: TypeName, tag: Option<string>, definition: Option<FunctionDefinition>)
  {
    predicate SignatureWellFormed(b3: Program) {
      // parameters have legal names and valid types
      && (forall p <- parameters :: LegalVariableName(p.name) && b3.IsType(p.typ))
      // formal parameters have distinct names
      && FParameter.UniqueNames(parameters)
    }

    predicate WellFormed(b3: Program) {
      && SignatureWellFormed(b3)
      && match definition {
        case None => true
        case Some(def) =>
          // set up the scopes
          var bodyScope := set p <- parameters :: p.name;
          var whenScope := bodyScope; // TODO: add the `forall` variables when these are parsed
          def.WellFormed(b3, whenScope, bodyScope)
      }
    }
  }

  datatype FParameter = FParameter(name: string, injective: bool, typ: TypeName)
  {
    static predicate UniqueNames(parameters: seq<FParameter>) {
      && (forall i, j :: 0 <= i < j < |parameters| ==> parameters[i].name != parameters[j].name)
    }
  }

  datatype FunctionDefinition = FunctionDefinition(when: seq<Expr>, body: Expr)
  {
    predicate WellFormed(b3: Program, whenScope: set<string>, bodyScope: set<string>) {
      // when-conditions are well-formed
      && (forall e <- when :: e.WellFormed(b3, whenScope))
      // body is well-formed
      && (body.WellFormed(b3, bodyScope))
    }
  }

  // Axioms

  datatype Axiom = Axiom(explains: seq<string>, expr: Expr)
  {
    predicate WellFormed(b3: Program, scope: Scope) {
      expr.WellFormed(b3, scope)
    }
  }

  // Procedures

  datatype Procedure = Procedure(name: string, parameters: seq<Parameter>, pre: seq<AExpr>, post: seq<AExpr>, body: Option<Stmt>)
  {
    function AllParameterNames(): set<string> {
      (set p <- parameters :: p.name) + (set p <- parameters | p.mode == InOut :: OldName(p.name))
    }

    predicate SignatureWellFormed(b3: Program) {
      // parameters have legal names and valid types
      && (forall p <- parameters :: LegalVariableName(p.name) && b3.IsType(p.typ))
      // formal parameters have distinct names
      && Parameter.UniqueNames(parameters)
      // set up the scopes: precondition, postcondition, body
      && var preScope := set p <- parameters | p.mode.IsIncoming() :: p.name;
      && var postScope := AllParameterNames();
      // pre- and postconditions are well-formed
      && (forall ae <- pre :: ae.WellFormed(b3, preScope))
      && (forall ae <- post :: ae.WellFormed(b3, postScope))
    }
    
    predicate WellFormed(b3: Program) {
      && SignatureWellFormed(b3)
      // body, if any, is well-formed
      && var postScope := AllParameterNames();
      && (body == None || body.value.WellFormed(b3, postScope, {}, false))
    }
  }

  type Scope = set<string>

  datatype Variable = Variable(name: string, isMutable: bool, optionalType: Option<TypeName>) // TODO: add auto-invariant
  {
    static predicate UniqueNames(variables: seq<Variable>) {
      forall i, j :: 0 <= i < j < |variables| ==> variables[i].name != variables[j].name
    }

    static predicate UniquelyNamed(variables: set<Variable>) {
      forall v0 <- variables, v1 <- variables :: v0.name == v1.name ==> v0 == v1
    }
  }

  datatype Parameter = Parameter(name: string, mode: ParameterMode, typ: TypeName)
  {
    static predicate UniqueNames(parameters: seq<Parameter>) {
      && (forall i, j :: 0 <= i < j < |parameters| ==> parameters[i].name != parameters[j].name)
    }

    static predicate UniquelyNamed(parameters: set<Parameter>) {
      forall p0 <- parameters, p1 <- parameters :: p0.name == p1.name ==> p0 == p1
    }
  }

  datatype ParameterMode = In | InOut | Out
  {
    predicate IsIncoming() {
      this in {In, InOut}
    }
    predicate IsOutgoing() {
      this in {InOut, Out}
    }

    function ToString(): string {
      match this
      case In => "in"
      case InOut => "inout"
      case Out => "out"
    }
  }

  const OldPrefix: string := "old$"

  function OldName(name: string): string {
    OldPrefix + name
  }

  predicate LegalVariableName(name: string) {
    !("_" <= name) &&
    !(OldPrefix <= name)
  }

  // Statements

  datatype Stmt =
    | VarDecl(v: Variable, init: Option<Expr>, body: Stmt)
    | Assign(lhs: string, rhs: Expr)
    | Block(stmts: seq<Stmt>)
    | Call(name: string, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr)
    | Assume(cond: Expr)
    | Assert(cond: Expr)
    | AForall(name: string, typ: TypeName, body: Stmt)
    // Control flow
    | Choose(branches: seq<Stmt>)
    | If(cond: Expr, thn: Stmt, els: Stmt)
    | IfCase(cases: seq<Case>)
    | Loop(invariants: seq<AExpr>, body: Stmt)
    | LabeledStmt(lbl: string, body: Stmt)
    | Exit(maybeLabel: Option<string>)
    | Return
    // Error reporting
    | Probe(e: Expr)
  {
    predicate ContainsAssertions() {
      match this
      case VarDecl(_, _, body) =>
        body.ContainsAssertions()
      case Block(stmts) =>
        exists s <- stmts :: s.ContainsAssertions()
      case Check(_) => true
      case Assume(_) => true
      case Assert(_) => true
      case AForall(_, _, _) => true
      case If(_, thn, els) =>
        thn.ContainsAssertions() || els.ContainsAssertions()
      case IfCase(cases) =>
        exists c <- cases :: c.body.ContainsAssertions()
      case Loop(_, body) =>
        body.ContainsAssertions()
      case LabeledStmt(_, body) =>
        body.ContainsAssertions()
      case _=> false
    }

    predicate ContainsNonAssertions() {
      match this
      case VarDecl(_, _, body) =>
        body.ContainsNonAssertions()
      case Assign(_, _) => true
      case Block(stmts) =>
        exists s <- stmts :: s.ContainsNonAssertions()
      case Call(_, _) => true
      case If(_, thn, els) =>
        thn.ContainsNonAssertions() || els.ContainsNonAssertions()
      case IfCase(cases) =>
        exists c <- cases :: c.body.ContainsNonAssertions()
      case Loop(_, _) => true // loops are not allowed in assertions
      case LabeledStmt(_, _) => true // assertions are not allowed to be labeled
      case Exit(_) => true
      case Return => true
      case Probe(_) => true
      case _ => false
    }

    predicate WellFormed(b3: Program, scope: Scope, labels: set<string>, insideLoop: bool) {
      match this
      case VarDecl(v, init, body) =>
        && LegalVariableName(v.name)
        && (v.optionalType.Some? ==> b3.IsType(v.optionalType.value))
        && (init.Some? ==> init.value.WellFormed(b3, scope))
        && (v.optionalType.Some? || init.Some?)
        && body.WellFormed(b3, scope + {v.name}, labels, insideLoop)
      case Assign(lhs, rhs) =>
        && lhs in scope
        && rhs.WellFormed(b3, scope)
      case Block(stmts) =>
        forall stmt <- stmts :: stmt.WellFormed(b3, scope, labels, insideLoop)
      case Call(name, args) =>
        // the call goes to a procedure in the program
        exists proc <- b3.procedures | name == proc.name ::
          // the number of arguments agrees with the number of formal parameters
          && |args| == |proc.parameters|
          // the parameter modes match
          && (forall i :: 0 <= i < |proc.parameters| ==> args[i].mode == proc.parameters[i].mode)
          // the arguments are well-formed
          && (forall i :: 0 <= i < |args| ==> args[i].arg.WellFormed(b3, scope))
      case Check(cond) =>
        cond.WellFormed(b3, scope)
      case Assume(cond) =>
        cond.WellFormed(b3, scope)
      case Assert(cond) =>
        cond.WellFormed(b3, scope)
      case AForall(name, typ, body) =>
        && LegalVariableName(name)
        && b3.IsType(typ)
        && body.WellFormed(b3, scope + {name}, labels, insideLoop)
      case Choose(branches) =>
        && |branches| != 0
        && forall branch <- branches :: branch.WellFormed(b3, scope, labels, insideLoop)
      case If(cond, thn, els) =>
        && cond.WellFormed(b3, scope)
        && thn.WellFormed(b3, scope, labels, insideLoop)
        && els.WellFormed(b3, scope, labels, insideLoop)
      case IfCase(cases) =>
        && |cases| != 0
        && forall cs <- cases ::
            && cs.cond.WellFormed(b3, scope)
            && cs.body.WellFormed(b3, scope, labels, insideLoop)
      case Loop(invariants, body) =>
        && (forall ae <- invariants :: ae.WellFormed(b3, scope))
        && body.WellFormed(b3, scope, labels, true)
      case LabeledStmt(lbl, body) =>
        && lbl !in labels
        && body.WellFormed(b3, scope, labels + {lbl}, insideLoop)
      case Exit(optionalLabel) =>
        match optionalLabel {
          case Some(lbl) => lbl in labels
          case None => insideLoop
        }
      case Return =>
        true
      case Probe(e) =>
        e.WellFormed(b3, scope)
    }

    predicate IsEmptyBlock() {
      Block? && |stmts| == 0
    }
  }

  datatype CallArgument = CallArgument(mode: ParameterMode, arg: Expr)

  datatype Case = Case(cond: Expr, body: Stmt)

  datatype AExpr =
    | AExpr(e: Expr)
    | AAssertion(s: Stmt)
  {
    predicate WellFormed(b3: Program, scope: Scope) {
      match this
      case AExpr(e) =>
        e.WellFormed(b3, scope)
      case AAssertion(s) =>
        s.WellFormed(b3, scope, {}, false)
    }

    ghost predicate Valid() {
      AAssertion? ==> ValidAssertionStatement(s)
    }
  }

  // ValidAssertionStatement(s) is a deep version of !s.ContainsNonAssertions()
  ghost predicate ValidAssertionStatement(s: Stmt) {
    match s
    case VarDecl(v, init, body) =>
      !v.isMutable && init.Some? && ValidAssertionStatement(body)
    case Check(_) =>
      true
    case Assume(e) =>
      true
    case Assert(e) =>
      true
    case AForall(_, _, body) =>
      ValidAssertionStatement(body)
    case Block(stmts) =>
      forall s <- stmts :: ValidAssertionStatement(s)
    case If(cond, thn, els) =>
      ValidAssertionStatement(thn) && ValidAssertionStatement(els)
    case IfCase(cases) =>
      forall c <- cases :: ValidAssertionStatement(c.body)
    case _ =>
      false
  }

  // Expressions

  datatype Operator =
    // ternary operators
    | IfThenElse
    // binary operators
    | Equiv
    | LogicalImp
    | LogicalAnd | LogicalOr
    | Eq | Neq
    | Less | AtMost
    | Plus | Minus | Times | Div | Mod
    // unary operators
    | LogicalNot
    | UnaryMinus
  {
    function ArgumentCount(): nat {
      match this
      case IfThenElse => 3
      case LogicalNot | UnaryMinus => 1
      case _ => 2
    }

    function ToString(): string {
      match this
      case IfThenElse => "if-then-else" // this case can be used in output (e.g., error messages), but does not lead to parseable syntax
      case Equiv => "<==>"
      case LogicalImp => "==>"
      case LogicalAnd => "&&"
      case LogicalOr => "||"
      case Eq => "=="
      case Neq => "!="
      case Less => "<"
      case AtMost => "<="
      case Plus => "+"
      case Minus | UnaryMinus => "-"
      case Times => "*"
      case Div => "/"
      case Mod => "%"
      case LogicalNot => "!"
    }

    static const EndlessOperatorBindingStrength: nat := 10

    function BindingStrength(): nat {
      match this
      case IfThenElse => EndlessOperatorBindingStrength
      case Equiv => 20
      case LogicalImp => 30
      case LogicalAnd | LogicalOr => 40
      case Eq | Neq | Less | AtMost => 50
      case Plus | Minus => 60
      case Times | Div | Mod => 70
      case LogicalNot | UnaryMinus => 80
    }
  }

  datatype Expr =
    | BLiteral(bvalue: bool)
    | ILiteral(ivalue: int)
    | CustomLiteral(s: string, typ: TypeName)
    | IdExpr(name: string)
    | OperatorExpr(op: Operator, args: seq<Expr>)
    | FunctionCallExpr(name: string, args: seq<Expr>)
    | LabeledExpr(name: string, expr: Expr)
    | LetExpr(name: string, optionalType: Option<TypeName>, rhs: Expr, body: Expr)
    | QuantifierExpr(univ: bool, bindings: seq<Binding>, patterns: seq<Pattern>, body: Expr)
  {
    predicate WellFormed(b3: Program, scope: Scope) {
      match this
      case BLiteral(_) => true
      case ILiteral(_) => true
      case CustomLiteral(_, _) => true
      case IdExpr(name) => name in scope
      case OperatorExpr(_, args) =>
        forall e <- args :: e.WellFormed(b3, scope)
      case FunctionCallExpr(name, args) =>
        // TODO: name
        forall e <- args :: e.WellFormed(b3, scope)
      case LabeledExpr(name, expr) =>
        // TODO: name
        expr.WellFormed(b3, scope)
      case LetExpr(name, typ, rhs, body) =>
        && rhs.WellFormed(b3, scope)
        && body.WellFormed(b3, scope + {name})
      case QuantifierExpr(_, bindings, patterns, body) =>
        var scope' := scope + set binding <- bindings :: binding.name;
        && (forall tr <- patterns :: tr.WellFormed(b3, scope'))
        && body.WellFormed(b3, scope')
    }
  }

  datatype Binding = Binding(name: string, typ: TypeName)

  datatype Pattern = Pattern(exprs: seq<Expr>) {
    predicate WellFormed(b3: Program, scope: Scope) {
      forall e <- exprs :: e.WellFormed(b3, scope)
    }
  }
}