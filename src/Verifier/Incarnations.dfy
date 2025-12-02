module Incarnations {
  import opened Std.Wrappers
  import opened Basics
  import opened Ast
  import opened SolverExpr
  import Types
  import RSolvers

  export
    reveals DeclMappings
    provides DeclMappings.Type2SType, DeclMappings.Type2STypeWithMap
    provides Incarnations, Incarnations.Print
    provides Incarnations.Empty, Incarnations.DeclMap
    provides Incarnations.Update, Incarnations.Reserve, Incarnations.Variables, Incarnations.DomainRestrict
    provides Incarnations.Set, Incarnations.CreateSubMap
    provides Incarnations.Get, Incarnations.REval, Incarnations.SubstituteVariable, Incarnations.Type2SType
    provides Types, Ast, SolverExpr, RSolvers

  type RExpr = RSolvers.RExpr

  datatype DeclMappings = DeclMappings(typeMap: map<TypeDecl, STypeDecl>, functionMap: map<Function, STypedDeclaration>)
  {
    function Type2SType(typ: Type): SType {
      Type2STypeWithMap(typ, typeMap)
    }

    static function Type2STypeWithMap(typ: Type, typeMap: map<TypeDecl, STypeDecl>): SType {
      match typ
      case BoolType => SBool
      case IntType | TagType => SInt
      case UserType(decl) =>
        var _ := Expect(decl in typeMap, decl.Name);
        var sTypeDecl := typeMap[decl];
        SUserType(sTypeDecl)
    }
  }

  function Expect(b: bool, msg: string): ()
    ensures b
  {
    assume {:axiom} b;
    ()
  } by method {
    expect b, msg;
    return ();
  }

  datatype Incarnations = Incarnations(nextSequenceCount: map<string, nat>, m: map<Variable, SConstant>, declMap: DeclMappings)
  {
    static function Empty(declMap: DeclMappings): Incarnations {
      Incarnations(map[], map[], declMap)
    }

    function DeclMap(): DeclMappings {
      declMap
    }

    method Print(header: string := "") {
      print "==== Incarnations: ", header, "\n";

      print "  nextSequenceCount:\n";
      var ss := nextSequenceCount.Keys;
      while ss != {} {
        var s :| s in ss;
        ss := ss - {s};
        print "    ", s, " := ", nextSequenceCount[s], "\n";
      }

      print "  m:\n";
      var vv := m.Keys;
      while vv != {} {
        var v: Variable :| v in vv;
        vv := vv - {v};
        print "    ", v.name, " := ", m[v].name, "\n";
      }
    }

    function Type2SType(typ: Type): SType {
      declMap.Type2SType(typ)
    }

    function Variables(): set<Variable> {
      m.Keys
    }

    function Get(v: Variable): SConstant {
      var _ := Expect(v in m, v.name);
      m[v]
    }

    // `Set` is intended to be used only during custom initializations of an Incarnations.
    function Set(v: Variable, sv: SConstant): Incarnations {
      this.(nextSequenceCount := map[v.name := 0] + nextSequenceCount, m := m[v := sv])
    }

    // `Set` is intended to be used only during custom initializations of an Incarnations.
    function CreateSubMap(customMap: map<Variable, SConstant>): Incarnations {
      Incarnations(nextSequenceCount, customMap, declMap)
    }

    method ReserveAux(v: Variable) returns (next: nat, x: SConstant) {
      var name := v.name;
      if name in nextSequenceCount.Keys {
        var n := nextSequenceCount[name];
        name := name + "%" + Int2String(n);
        next := n + 1;
      } else {
        next := 0;
      }
      x := new SConstant(name, declMap.Type2SType(v.typ));
    }

    method Reserve(v: Variable) returns (incarnations: Incarnations, x: SConstant) {
      var nextSequenceNumber;
      nextSequenceNumber, x := ReserveAux(v);
      incarnations := this.(nextSequenceCount := nextSequenceCount[v.name := nextSequenceNumber]);
    }

    method Update(v: Variable) returns (incarnations: Incarnations, x: SConstant) {
      var nextSequenceNumber;
      nextSequenceNumber, x := ReserveAux(v);
      incarnations := this.(nextSequenceCount := nextSequenceCount[v.name := nextSequenceNumber], m := m[v := x]);
    }

    function DomainRestrict(variables: set<Variable>): Incarnations {
      var m' := map v <- m.Keys | v in variables :: m[v];
      this.(m := m')
    }

    method CreateForBoundVariables(expr: Expr) returns (r: Incarnations)
      decreases expr
    {
      r := this;
      match expr
      case BLiteral(_) =>
      case ILiteral(_) =>
      case CustomLiteral(_, _) =>
      case IdExpr(_) =>
      case OperatorExpr(_, args) =>
        for i := 0 to |args| {
          r := r.CreateForBoundVariables(args[i]);
        }
      case FunctionCallExpr(_, args) =>
        for i := 0 to |args| {
          r := r.CreateForBoundVariables(args[i]);
        }
      case LabeledExpr(_, body) =>
        r := r.CreateForBoundVariables(body);
      case LetExpr(v, rhs, body) =>
        r := r.CreateForBoundVariables(rhs);
        expect v !in r.m.Keys;
        var sVar;
        r, sVar := Update(v);
        r := r.CreateForBoundVariables(body);
      case QuantifierExpr(_, vv, patterns, body) =>
        expect forall v <- vv :: v !in r.m.Keys;
        r := this;
        for i := 0 to |vv| {
          var sVar;
          r, sVar := r.Update(vv[i]);
        }
        for i := 0 to |patterns| {
          var pattern := patterns[i];
          for j := 0 to |pattern.exprs| {
            r := r.CreateForBoundVariables(pattern.exprs[j]);
          }
        }
        r := r.CreateForBoundVariables(body);
      case ClosureExpr(_, _, _, _) =>
        // Closures must be elaborated before verification
        expect false;
    }

    // Create SConstant's for the bound variables in "expr" and then substitute these and the other incarnations
    // into "expr".
    method REval(expr: Expr) returns (r: RSolvers.RExpr)
      requires expr.WellFormed()
    {
      var incarnations := CreateForBoundVariables(expr);
      r := incarnations.Substitute(expr);
    }

    function SubstituteVariable(v: Variable): SConstant {
      var _ := Expect(v in m, v.name);
      m[v]
    }

    function Substitute(expr: Expr): RSolvers.RExpr
      requires expr.WellFormed()
    {
      match expr
      case BLiteral(value) => RExpr.Boolean(value)
      case ILiteral(value) => RExpr.Integer(value)
      case CustomLiteral(s, typ) => RExpr.CustomLiteral(s, declMap.Type2SType(typ))
      case IdExpr(v) =>
        var sv := SubstituteVariable(v);
        RExpr.Id(sv)
      case OperatorExpr(op, args) =>
        var rArgs := SubstituteList(args);
        match op {
          case IfThenElse =>
            RExpr.IfThenElse(rArgs[0], rArgs[1], rArgs[2])
          case Neq =>
            var eq := RExpr.FuncAppl(RExpr.Operator2ROperator(Operator.Eq), rArgs);
            RExpr.FuncAppl(RExpr.Operator2ROperator(Operator.LogicalNot), [eq])
          case _ =>
            RExpr.FuncAppl(RExpr.Operator2ROperator(op), rArgs)
        }
      case FunctionCallExpr(func, args) =>
        var rArgs := SubstituteList(args);
        var _ := Expect(func in declMap.functionMap, func.Name);
        var f := declMap.functionMap[func];
        RExpr.FuncAppl(RSolvers.UserDefinedFunction(func, f, None), rArgs)
      case LabeledExpr(_, body) =>
        // TODO: do something with the label
        Substitute(body)
      case LetExpr(v, rhs, body) =>
        var _ := Expect(v in m, v.name);
        var sVar := m[v];
        RExpr.LetExpr(sVar, Substitute(rhs), Substitute(body))
      case QuantifierExpr(univ, vv, patterns, body) =>
        var _ := Expect(forall v <- vv :: v in m, "quantifier-vars");
        var sVars := SeqMap(vv, v requires v in m => m[v]);
        var trs := SubstitutePatterns(patterns);
        var b := Substitute(body);
        RExpr.QuantifierExpr(univ, sVars, trs, b)
      case ClosureExpr(_, _, _, _) =>
        // Closures must be elaborated before verification
        var _ := Expect(false, "closure-not-elaborated");
        RExpr.Boolean(false)  // unreachable
    }

    function SubstituteList(exprs: seq<Expr>): seq<RSolvers.RExpr>
      requires forall expr <- exprs :: expr.WellFormed()
      ensures |SubstituteList(exprs)| == |exprs|
    {
      if exprs == [] then
        []
      else
        [Substitute(exprs[0])] + SubstituteList(exprs[1..])
    }

    function SubstitutePatterns(patterns: seq<Pattern>): seq<RSolvers.RPattern>
      requires forall tr <- patterns :: tr.WellFormed()
    {
      if patterns == [] then
        []
      else
        assert patterns[0].WellFormed();
        [RSolvers.RPattern(SubstituteList(patterns[0].exprs))] + SubstitutePatterns(patterns[1..])
    }
  }

}