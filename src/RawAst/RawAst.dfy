module RawAst {
  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import PrintUtil

  // Top-level program

  // A raw program reflects program that has been parsed.
  datatype Program = Program(types: seq<TypeName>, datatypes: seq<DatatypeDecl>, taggers: seq<Tagger>, functions: seq<Function>, axioms: seq<Axiom>, procedures: seq<Procedure>)
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
      // datatype names do not use the names of built-in types
      && (forall dt <- datatypes :: dt.name !in BuiltInTypes)
      // datatype names do not conflict with user-defined types
      && (forall dt <- datatypes :: dt.name !in types)
      // datatype names are unique
      && (forall i, j :: 0 <= i < j < |datatypes| ==> datatypes[i].name != datatypes[j].name)
      // datatype declarations are well-formed
      && (forall dt <- datatypes :: dt.WellFormed(this))
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

  // Datatypes

  datatype ConstructorField = ConstructorField(name: string, typ: TypeName)

  datatype Constructor = Constructor(name: string, fields: seq<ConstructorField>)
  {
    predicate WellFormed(b3: Program) {
      // field names are unique within the constructor
      && (forall i, j :: 0 <= i < j < |fields| ==> fields[i].name != fields[j].name)
      // field names are legal variable names
      && (forall f <- fields :: LegalVariableName(f.name))
      // field types are valid
      && (forall f <- fields :: b3.IsType(f.typ))
    }
  }

  datatype DatatypeDecl = DatatypeDecl(name: string, constructors: seq<Constructor>)
  {
    predicate WellFormed(b3: Program) {
      // constructor names are unique within the datatype
      && (forall i, j :: 0 <= i < j < |constructors| ==> constructors[i].name != constructors[j].name)
      // each constructor is well-formed
      && (forall c <- constructors :: c.WellFormed(b3))
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

  datatype Procedure = Procedure(name: string, parameters: seq<PParameter>, pre: seq<AExpr>, post: seq<AExpr>, body: Option<Stmt>)
  {
    function AllParameterNames(): set<string> {
      (set p <- parameters :: p.name) + (set p <- parameters | p.mode == InOut :: OldName(p.name))
    }

    predicate SignatureWellFormed(b3: Program) {
      // parameters have legal names and valid types
      && (forall p <- parameters :: LegalVariableName(p.name) && b3.IsType(p.typ))
      // formal parameters have distinct names
      && PParameter.UniqueNames(parameters)
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

  datatype Variable = Variable(name: string, isMutable: bool, optionalType: Option<TypeName>, optionalAutoInv: Option<Expr>)
  {
    static predicate UniqueNames(variables: seq<Variable>) {
      forall i, j :: 0 <= i < j < |variables| ==> variables[i].name != variables[j].name
    }

    static predicate UniquelyNamed(variables: set<Variable>) {
      forall v0 <- variables, v1 <- variables :: v0.name == v1.name ==> v0 == v1
    }
  }

  datatype PParameter = PParameter(name: string, mode: ParameterMode, typ: TypeName, optionalAutoInv: Option<Expr>)
  {
    static predicate UniqueNames(parameters: seq<PParameter>) {
      && (forall i, j :: 0 <= i < j < |parameters| ==> parameters[i].name != parameters[j].name)
    }

    static predicate UniquelyNamed(parameters: set<PParameter>) {
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

  const OldPrefix: string := "old!"

  function OldName(name: string): string {
    OldPrefix + name
  }

  function FromOldName(name: string): Option<string> {
    if OldPrefix <= name then
      Some(name[|OldPrefix|..])
    else
      None
  }

  predicate LegalVariableName(name: string) {
    && name != []
    && !("_" <= name)
    && !(OldPrefix <= name)
    && name != "tag"
  }

  // This lemma gives easy ways to prove that a string is legal as a variable name.
  lemma SurelyLegalVariableName(name: string)
    requires name != [] && name[0] == 's'
    ensures LegalVariableName(name)
  {
  }

  // Statements

  datatype Stmt =
    | VarDecl(v: Variable, init: Option<Expr>, body: Stmt)
    | Assign(lhs: string, rhs: Expr)
    | Reinit(vars: seq<string>)
    | Block(stmts: seq<Stmt>)
    | Call(name: string, args: seq<CallArgument>)
    // assertions
    | Check(cond: Expr)
    | Assume(cond: Expr)
    | Reach(cond: Expr)
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
      case Reinit(vars) =>
        forall name <- vars :: name in scope
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
      case Reach(cond) =>
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
      case Div => "div"
      case Mod => "mod"
      case LogicalNot => "!"
    }

    function BindingStrength(): PrintUtil.BindingPower {
      match this
      case IfThenElse => PrintUtil.BindingPower.EndlessOperator
      case Equiv => PrintUtil.BindingPower(20, 20)
      case LogicalImp => PrintUtil.BindingPower(31, 30)
      case LogicalAnd => PrintUtil.BindingPower(40, 40, PrintUtil.SameFamilyWins(0))
      case LogicalOr => PrintUtil.BindingPower(40, 40, PrintUtil.SameFamilyWins(1))
      case Eq | Neq | Less | AtMost => PrintUtil.BindingPower(50, 50, PrintUtil.ContextWins)
      case Plus => PrintUtil.BindingPower(60, 60)
      case Minus => PrintUtil.BindingPower(60, 61)
      case Times => PrintUtil.BindingPower(70, 70)
      case Div | Mod => PrintUtil.BindingPower(70, 71)
      case LogicalNot | UnaryMinus => PrintUtil.BindingPower(80, 80)
    }
  }

  datatype Expr =
    | BLiteral(bvalue: bool)
    | ILiteral(ivalue: int)
    | CustomLiteral(s: string, typ: TypeName)
    | IdExpr(name: string, isOld: bool := false)
    | OperatorExpr(op: Operator, args: seq<Expr>)
    | FunctionCallExpr(name: string, args: seq<Expr>)
    | LabeledExpr(name: string, expr: Expr)
    | LetExpr(name: string, optionalType: Option<TypeName>, rhs: Expr, body: Expr)
    | QuantifierExpr(univ: bool, bindings: seq<Binding>, patterns: seq<Pattern>, body: Expr)
    | ClosureExpr(closureBindings: seq<ClosureBinding>, resultVar: string, resultType: TypeName, properties: seq<ClosureProperty>)
  {
    predicate WellFormed(b3: Program, scope: Scope) {
      match this
      case BLiteral(_) => true
      case ILiteral(_) => true
      case CustomLiteral(_, _) => true
      case IdExpr(name, isOld) =>
        (if isOld then OldName(name) else name) in scope
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
      case ClosureExpr(closureBindings, resultVar, resultType, properties) =>
        && b3.IsType(resultType)
        && (forall b <- closureBindings :: b.WellFormed(b3, scope))
        && (forall p <- properties :: p.WellFormed(b3, scope, closureBindings))
    }
  }

  datatype Binding = Binding(name: string, typ: TypeName)

  datatype Pattern = Pattern(exprs: seq<Expr>) {
    predicate WellFormed(b3: Program, scope: Scope) {
      forall e <- exprs :: e.WellFormed(b3, scope)
    }
  }

  datatype ClosureBinding = ClosureBinding(name: string, params: seq<Binding>, rhs: Expr)
  {
    predicate WellFormed(b3: Program, scope: Scope) {
      var bindingScope := scope + set p <- params :: p.name;
      && (forall p <- params :: LegalVariableName(p.name) && b3.IsType(p.typ))
      && rhs.WellFormed(b3, bindingScope)
    }
  }

  datatype ClosureProperty = ClosureProperty(triggers: seq<Pattern>, body: Expr)
  {
    predicate WellFormed(b3: Program, scope: Scope, bindings: seq<ClosureBinding>) {
      // Properties can reference closure binding parameters
      var bindingParams := set b <- bindings, p <- b.params :: p.name;
      var propertyScope := scope + bindingParams;
      && (forall tr <- triggers :: tr.WellFormed(b3, propertyScope))
      && body.WellFormed(b3, propertyScope)
    }
  }
}