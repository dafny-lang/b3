module ExprResolver {
  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import Raw = RawAst
  import opened Ast
  import opened TypeResolver
  import PrintUtil

  export
    reveals ExprResolverState, ExprResolverState.Valid
    provides ResolveExpr, ResolveExprList, ResolveMaybeExpr
    provides Wrappers, Raw, Ast, Types

  datatype ExprResolverState = ExprResolverState(b3: Raw.Program, typeMap: map<string, TypeDecl>, functionMap: map<string, Function>)
  {
    ghost predicate Valid() {
      forall typename :: b3.IsType(typename) <==> typename in BuiltInTypes || typename in typeMap
    }
  }

  method ResolveMaybeExpr(maybeExpr: Option<Raw.Expr>, ers: ExprResolverState, varMap: map<string, Variable>) returns (r: Result<Option<Expr>, string>)
    ensures r.Success? && maybeExpr.None? ==> r.value == None
    ensures r.Success? && maybeExpr.Some? ==> maybeExpr.value.WellFormed(ers.b3, varMap.Keys)
    ensures r.Success? && maybeExpr.Some? ==> r.value.Some? && r.value.value.WellFormed()
  {
    match maybeExpr
    case None =>
      return Success(None);
    case Some(expr) =>
      var e :- ResolveExpr(expr, ers, varMap);
      return Success(Some(e));
  }

  method ResolveExpr(expr: Raw.Expr, ers: ExprResolverState, varMap: map<string, Variable>) returns (result: Result<Expr, string>)
    ensures result.Success? ==> expr.WellFormed(ers.b3, varMap.Keys)
    ensures result.Success? ==> result.value.WellFormed()
    decreases expr, 1
  {
    var r: Expr;
    match expr {
      case BLiteral(value) =>
        r := BLiteral(value);
      case ILiteral(value) =>
        r := ILiteral(value);
      case CustomLiteral(s, typeName) =>
        var typ :- ResolveType(typeName, ers.typeMap);
        if typ == BoolType || typ == IntType {
          return Failure("custom literal is not allowed for a built-in type: " + PrintUtil.CustomLiteralToString(s, typeName));
        }
        r := CustomLiteral(s, typ);
      case IdExpr(name, isOld) =>
        var encodedName := if isOld then Raw.OldName(name) else name;
        if encodedName in varMap {
          r := IdExpr(varMap[encodedName]);
        } else if !isOld || name !in varMap {
          return Failure("undeclared variable: " + name);
        } else {
          var origVar := varMap[name];
          return Failure("variable '" + name + "' cannot be used with 'old'; only inout-parameters can be, and only in two-state contexts");
        }
      case OperatorExpr(op, args) =>
        if |args| != op.ArgumentCount() {
          return Failure("operator " + op.ToString() + " expects " + Int2String(op.ArgumentCount()) + " arguments, got " + Int2String(|args|));
        }
        var resolvedArgs :- ResolveExprList(args, ers, varMap);
        r := OperatorExpr(op, resolvedArgs);
      case FunctionCallExpr(name, args) =>
        if name !in ers.functionMap {
          return Failure("undeclared function: " + name);
        }
        var func := ers.functionMap[name];
        if |args| != |func.Parameters| {
          return Failure("wrong number of arguments in call to function " + name);
        }
        var resolvedArgs :- ResolveExprList(args, ers, varMap);
        r := FunctionCallExpr(func, resolvedArgs);
      case LabeledExpr(name, body) =>
        var lbl := new Label(name);
        var b :- ResolveExpr(body, ers, varMap);
        r := LabeledExpr(lbl, b);
      case LetExpr(name, optionalTypeName, rhs, body) =>
        if !Raw.LegalVariableName(name) {
          return Failure("illegal variable name: " + name);
        }
        var rRhs :- ResolveExpr(rhs, ers, varMap);
        var typ;
        match optionalTypeName {
          case None =>
            typ := rRhs.ExprType();
          case Some(typeName) =>
            typ :- ResolveType(typeName, ers.typeMap);
        }
        var letVariable := new LocalVariable(name, false, typ);
        var varMap' := varMap[name := letVariable];
        assert varMap'.Keys == varMap.Keys + {name};
        var rBody :- ResolveExpr(body, ers, varMap');
        r := LetExpr(letVariable, rRhs, rBody);
      case QuantifierExpr(univ, bindings, patterns, body) =>
        var boundVars, varMap' := [], varMap;
        var namesIntroduced := {};
        for n := 0 to |bindings|
          invariant varMap'.Keys == varMap.Keys + set binding <- bindings[..n] :: binding.name
        {
          var binding := bindings[n];
          if !Raw.LegalVariableName(binding.name) {
            return Failure("illegal variable name: " + binding.name);
          } else if binding.name in namesIntroduced {
            return Failure("duplicate variable name in quantifier: " + binding.name);
          }
          namesIntroduced := namesIntroduced + {binding.name};
          var typ :- ResolveType(binding.typ, ers.typeMap);
          var quantifiedVariable := new LocalVariable(binding.name, false, typ);
          boundVars := boundVars + [quantifiedVariable];
          varMap' := varMap'[binding.name := quantifiedVariable];
        }
        assert varMap'.Keys == varMap.Keys + set binding <- bindings :: binding.name;
        var b :- ResolveExpr(body, ers, varMap');
        var trs :- ResolvePatterns(patterns, ers, varMap');
        var _ :- CheckPatterns(trs, boundVars);
        r := QuantifierExpr(univ, boundVars, trs, b);
      case ClosureExpr(closureBindings, resultVar, resultType, properties) =>
        r :- ElaborateClosure(expr, ers, varMap);
    }
    return Success(r);
  }

  method ResolveExprList(exprs: seq<Raw.Expr>, ers: ExprResolverState, varMap: map<string, Variable>) returns (result: Result<seq<Expr>, string>)
    ensures result.Success? ==> forall expr <- exprs :: expr.WellFormed(ers.b3, varMap.Keys)
    ensures result.Success? ==> |result.value| == |exprs|
    ensures result.Success? ==> forall expr <- result.value :: expr.WellFormed()
  {
    var resolvedExprs := [];
    for n := 0 to |exprs|
      invariant forall expr <- exprs[..n] :: expr.WellFormed(ers.b3, varMap.Keys)
      invariant |resolvedExprs| == n
      invariant forall expr: Expr <- resolvedExprs :: expr.WellFormed()
    {
      var r :- ResolveExpr(exprs[n], ers, varMap);
      resolvedExprs := resolvedExprs + [r];
    }
    return Success(resolvedExprs);
  }

  method ResolvePatterns(patterns: seq<Raw.Pattern>, ers: ExprResolverState, varMap: map<string, Variable>) returns (result: Result<seq<Pattern>, string>)
    ensures result.Success? ==> forall tr <- patterns :: tr.WellFormed(ers.b3, varMap.Keys)
    ensures result.Success? ==> forall tr <- result.value :: tr.WellFormed()
  {
    var resolvedPatterns := [];
    for n := 0 to |patterns|
      invariant forall tr <- patterns[..n] :: tr.WellFormed(ers.b3, varMap.Keys)
      invariant forall tr: Pattern <- resolvedPatterns :: tr.WellFormed()
    {
      var exprs :- ResolveExprList(patterns[n].exprs, ers, varMap);
      resolvedPatterns := resolvedPatterns + [Pattern(exprs)];
    }
    return Success(resolvedPatterns);
  }

  method CheckPatterns(patterns: seq<Pattern>, boundVariables: seq<Variable>) returns (result: Result<(), string>) {
    for i := 0 to |patterns| {
      var pattern := patterns[i];
      if exists e <- pattern.exprs :: ContainsQuantifiers(e) {
        return Failure("a pattern is not allowed to contain quantifiers");
      }
      var variablesUsedInPattern := Expr.FreeVariablesInList(pattern.exprs);
      for i := 0 to |boundVariables| {
        var bv := boundVariables[i];
        if bv !in variablesUsedInPattern {
          return Failure("a pattern must mention all bound variables of the quantifier but doesn't mention '" + bv.name + "'");
        }
      }
    }
    return Success(());
  }

  predicate ContainsQuantifiers(expr: Expr) {
    match expr
    case BLiteral(_) => false
    case ILiteral(_) => false
    case CustomLiteral(_, _) => false
    case IdExpr(_) => false
    case OperatorExpr(_, args) =>
      exists e <- args :: ContainsQuantifiers(e)
    case FunctionCallExpr(_, args) =>
      exists e <- args :: ContainsQuantifiers(e)
    case LabeledExpr(_, body) =>
      ContainsQuantifiers(body)
    case LetExpr(v, rhs, body) =>
      ContainsQuantifiers(rhs) || ContainsQuantifiers(body)
    case QuantifierExpr(_, _, _, _) => true
    case ClosureExpr(_, _, _, _) => false  // Closures are elaborated away before this check
  }

  // ===== Closure Elaboration =====

  // Stub: Closure elaboration not yet implemented
  // TODO: Implement full elaboration
  method ElaborateClosure(
    closure: Raw.Expr,
    ers: ExprResolverState,
    varMap: map<string, Variable>
  ) returns (result: Result<Expr, string>)
    requires closure.ClosureExpr?
    ensures result.Success? ==> closure.WellFormed(ers.b3, varMap.Keys)
    ensures result.Success? ==> result.value.WellFormed()
    decreases closure, 0
  {
    return Failure("closure elaboration not yet fully implemented");
  }
}
