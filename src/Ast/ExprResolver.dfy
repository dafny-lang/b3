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
    requires ers.Valid()
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
    requires ers.Valid()
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
        r :- ResolveClosureExpr(expr, ers, varMap);
    }
    return Success(r);
  }

  method ResolveExprList(exprs: seq<Raw.Expr>, ers: ExprResolverState, varMap: map<string, Variable>) returns (result: Result<seq<Expr>, string>)
    requires ers.Valid()
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
    requires ers.Valid()
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

  // ===== Closure Resolution =====
  //
  // Closure resolution transforms a Raw.ClosureExpr into an Ast.ClosureExpr by:
  // 1. Resolving all type names to Ast.Type
  // 2. Resolving all variable references in binding expressions
  // 3. Resolving all expressions in closure properties
  //
  // The resolution follows specific scoping rules:
  // - Binding RHS expressions: outer scope + binding parameters (params can shadow outer vars)
  // - Property expressions: outer scope + result variable + binding names + binding parameters
  //
  // Example closure:
  //   lift %body(x: int) := Unbox(bx, x) into %s: Seq<int> by { %s == SeqBuild(n, %body) }
  //
  // Resolution scopes:
  // - Binding %body RHS: outer scope + {x: int}
  // - Property: outer scope + {%s: Seq<int>, %body: <type of Unbox(bx, x)>}

  /// Resolves a closure expression by:
  /// 1. Resolving the result type
  /// 2. Resolving each closure binding (with its parameters and RHS)
  /// 3. Resolving each closure property (with access to result var and binding names)
  /// 4. Creating the resolved Ast.ClosureExpr
  ///
  /// Requires ers.Valid() to prove that resolved types satisfy b3.IsType().
  method ResolveClosureExpr(
    closure: Raw.Expr,
    ers: ExprResolverState,
    varMap: map<string, Variable>
  ) returns (result: Result<Expr, string>)
    requires closure.ClosureExpr?
    requires ers.Valid()
    ensures result.Success? ==> closure.WellFormed(ers.b3, varMap.Keys)
    ensures result.Success? ==> result.value.WellFormed()
    decreases closure, 0
  {
    var closureBindings := closure.closureBindings;
    var resultVar := closure.resultVar;
    var resultTypeName := closure.resultType;
    var properties := closure.properties;

    // Step 1: Resolve the result type
    // ResolveType ensures: resultTypeName in BuiltInTypes || resultTypeName in ers.typeMap
    // ers.Valid() ensures: b3.IsType(typename) <==> typename in BuiltInTypes || typename in typeMap
    // Together these prove: ers.b3.IsType(resultTypeName)
    var resolvedResultType :- ResolveType(resultTypeName, ers.typeMap);
    assert ers.b3.IsType(resultTypeName);

    // Step 2: Resolve each closure binding
    // Each binding is resolved independently with its own parameter scope.
    // We track that resolved binding names match raw binding names (needed for property resolution).
    var resolvedBindings: seq<ClosureBinding> := [];
    for i := 0 to |closureBindings|
      invariant |resolvedBindings| == i
      invariant forall b <- resolvedBindings :: b.WellFormed()
      invariant forall j :: 0 <= j < i ==> closureBindings[j].WellFormed(ers.b3, varMap.Keys)
      invariant forall j :: 0 <= j < i ==> resolvedBindings[j].name == closureBindings[j].name
    {
      var binding := closureBindings[i];
      var resolvedBinding :- ResolveClosureBindingWithWF(binding, ers, varMap);
      resolvedBindings := resolvedBindings + [resolvedBinding];
    }
    assert forall b <- closureBindings :: b.WellFormed(ers.b3, varMap.Keys);
    assert forall j :: 0 <= j < |resolvedBindings| ==> resolvedBindings[j].name == closureBindings[j].name;

    // Step 3: Resolve closure properties
    // Properties are resolved in an extended scope that includes:
    // - The outer scope (varMap)
    // - The result variable (e.g., %s) with the result type
    // - Each closure binding name (e.g., %body) with the type of its RHS
    // - Binding parameters (e.g., x in %body(x: int) := e)
    var resolvedProperties: seq<ClosureProperty> := [];
    for i := 0 to |properties|
      invariant |resolvedProperties| == i
      invariant forall p <- resolvedProperties :: p.WellFormed()
      invariant forall j :: 0 <= j < i ==> properties[j].WellFormed(ers.b3, varMap.Keys, closureBindings, resultVar)
    {
      var prop := properties[i];
      var resolvedProp :- ResolveClosurePropertyWithWF(prop, ers, varMap, resultVar, resolvedResultType, resolvedBindings, closureBindings);
      resolvedProperties := resolvedProperties + [resolvedProp];
    }
    assert forall p <- properties :: p.WellFormed(ers.b3, varMap.Keys, closureBindings, resultVar);

    // Step 4: Create the resolved Ast.ClosureExpr
    // The resolved closure contains:
    // - resolvedBindings: bindings with resolved parameter types and RHS expressions
    // - resultVar: the result variable name (string, not Variable object)
    // - resolvedResultType: the resolved result type
    // - resolvedProperties: properties with resolved triggers and body expressions
    var resolvedClosure := ClosureExpr(resolvedBindings, resultVar, resolvedResultType, resolvedProperties);
    
    return Success(resolvedClosure);
  }

  /// Resolves a single closure binding and proves its raw well-formedness.
  ///
  /// A closure binding has the form: %name(p1: T1, ..., pn: Tn) := rhs_expr
  ///
  /// Resolution process:
  /// 1. Validate each parameter name is legal
  /// 2. Resolve each parameter type
  /// 3. Build a scope that includes outer scope + binding parameters
  /// 4. Resolve the RHS expression in this extended scope
  ///
  /// Scoping rule: Binding parameters CAN shadow outer scope variables.
  /// This allows patterns like: %body(x: int) := f(x) where x shadows an outer x.
  ///
  /// Postconditions ensure:
  /// - The resolved binding is well-formed (Ast.ClosureBinding.WellFormed)
  /// - The binding name is preserved (needed for property resolution)
  /// - The raw binding is well-formed (Raw.ClosureBinding.WellFormed)
  method ResolveClosureBindingWithWF(
    binding: Raw.ClosureBinding,
    ers: ExprResolverState,
    varMap: map<string, Variable>
  ) returns (result: Result<ClosureBinding, string>)
    requires ers.Valid()
    ensures result.Success? ==> result.value.WellFormed()
    ensures result.Success? ==> result.value.name == binding.name
    ensures result.Success? ==> binding.WellFormed(ers.b3, varMap.Keys)
  {
    var bindingName := binding.name;
    var params := binding.params;
    var rhs := binding.rhs;

    // Build the binding scope by adding parameters to the outer scope.
    // Parameters can shadow outer scope variables.
    var resolvedParams: seq<(string, Type)> := [];
    var bindingVarMap := varMap;
    var bindingScope := varMap.Keys;
    
    for i := 0 to |params|
      invariant |resolvedParams| == i
      invariant bindingVarMap.Keys == varMap.Keys + set p <- params[..i] :: p.name
      invariant bindingScope == varMap.Keys + set p <- params[..i] :: p.name
      invariant forall j :: 0 <= j < i ==> Raw.LegalVariableName(params[j].name) && ers.b3.IsType(params[j].typ)
    {
      var param := params[i];
      
      // Validate parameter name
      if !Raw.LegalVariableName(param.name) {
        return Failure("illegal variable name in closure binding parameter: " + param.name);
      }
      
      // Resolve parameter type (ers.Valid() ensures b3.IsType holds after successful resolution)
      var paramType :- ResolveType(param.typ, ers.typeMap);
      assert ers.b3.IsType(param.typ);
      
      resolvedParams := resolvedParams + [(param.name, paramType)];
      
      // Add parameter to scope (shadowing any outer variable with the same name)
      var paramVar := new LocalVariable(param.name, false, paramType);
      bindingVarMap := bindingVarMap[param.name := paramVar];
      bindingScope := bindingScope + {param.name};
    }
    
    // All parameters validated and added to scope
    assert forall p <- params :: Raw.LegalVariableName(p.name) && ers.b3.IsType(p.typ);
    assert bindingVarMap.Keys == varMap.Keys + set p <- params :: p.name;

    // Resolve the RHS expression in the extended scope (outer + parameters)
    var resolvedRhs :- ResolveExpr(rhs, ers, bindingVarMap);
    assert rhs.WellFormed(ers.b3, bindingVarMap.Keys);
    
    // Prove raw binding well-formedness
    // Raw.ClosureBinding.WellFormed requires:
    // - All params have legal names and valid types (proved above)
    // - RHS is well-formed in scope + param names (proved by ResolveExpr)
    assert binding.WellFormed(ers.b3, varMap.Keys) by {
      var expectedBindingScope := varMap.Keys + set p <- params :: p.name;
      assert bindingVarMap.Keys == expectedBindingScope;
    }

    return Success(ClosureBinding(bindingName, resolvedParams, resolvedRhs));
  }

  /// Resolves a single closure property and proves its raw well-formedness.
  ///
  /// A closure property is an expression (possibly with triggers) that describes
  /// the behavior of the closure result. Properties can reference:
  /// - Variables from the outer scope
  /// - The result variable (e.g., %s)
  /// - Closure binding names (e.g., %body) - treated as variables with RHS type
  /// - Binding parameters (e.g., x in %body(x: int) := e)
  ///
  /// Example property: %s == SeqBuild(n, %body)
  /// - %s is the result variable
  /// - %body is a closure binding name (used as a value here)
  ///
  /// The property scope must exactly match Raw.ClosureProperty.WellFormed's scope:
  ///   scope + {resultVar} + bindingNames + bindingParams
  ///
  /// Preconditions:
  /// - resolvedBindings and rawBindings have the same length
  /// - Corresponding bindings have the same name (for scope construction)
  method ResolveClosurePropertyWithWF(
    prop: Raw.ClosureProperty,
    ers: ExprResolverState,
    varMap: map<string, Variable>,
    resultVar: string,
    resultType: Type,
    resolvedBindings: seq<ClosureBinding>,
    rawBindings: seq<Raw.ClosureBinding>
  ) returns (result: Result<ClosureProperty, string>)
    requires ers.Valid()
    requires forall b <- resolvedBindings :: b.WellFormed()
    requires |resolvedBindings| == |rawBindings|
    requires forall i :: 0 <= i < |resolvedBindings| ==> resolvedBindings[i].name == rawBindings[i].name
    ensures result.Success? ==> result.value.WellFormed()
    ensures result.Success? ==> prop.WellFormed(ers.b3, varMap.Keys, rawBindings, resultVar)
  {
    // Compute the expected raw property scope for verification
    // This must match Raw.ClosureProperty.WellFormed's propertyScope definition
    var bindingNames := set b <- rawBindings :: b.name;
    var bindingParams := set b <- rawBindings, p <- b.params :: p.name;
    var rawPropertyScope := varMap.Keys + {resultVar} + bindingNames + bindingParams;

    // Build the property scope incrementally, tracking that we match rawPropertyScope
    var propertyVarMap := varMap;
    
    // 1. Add result variable to scope (e.g., %s: Seq<int>)
    var resultVariable := new LocalVariable(resultVar, false, resultType);
    propertyVarMap := propertyVarMap[resultVar := resultVariable];

    // 2. Add each closure binding name as a variable with the type of its RHS
    // This allows properties to reference binding names as values
    // e.g., %body in "%s == SeqBuild(n, %body)" has type of Unbox(bx, x)
    for i := 0 to |resolvedBindings|
      invariant propertyVarMap.Keys == varMap.Keys + {resultVar} + set j | 0 <= j < i :: resolvedBindings[j].name
    {
      var binding := resolvedBindings[i];
      var bindingType := binding.rhs.ExprType();
      var bindingVar := new LocalVariable(binding.name, false, bindingType);
      propertyVarMap := propertyVarMap[binding.name := bindingVar];
    }
    
    // Prove that resolved binding names == raw binding names (set equality)
    // This is needed because we built the scope using resolvedBindings but
    // need to prove well-formedness against rawBindings
    assert (set j | 0 <= j < |resolvedBindings| :: resolvedBindings[j].name) == bindingNames by {
      forall j | 0 <= j < |resolvedBindings|
        ensures resolvedBindings[j].name in bindingNames
      {
        assert resolvedBindings[j].name == rawBindings[j].name;
        assert rawBindings[j] in rawBindings;
      }
      forall b | b in rawBindings
        ensures b.name in (set k | 0 <= k < |resolvedBindings| :: resolvedBindings[k].name)
      {
        var idx :| 0 <= idx < |rawBindings| && rawBindings[idx] == b;
        assert resolvedBindings[idx].name == rawBindings[idx].name;
      }
    }
    
    assert propertyVarMap.Keys == varMap.Keys + {resultVar} + bindingNames;

    // 3. Add binding parameters to scope
    // Properties can reference binding parameters (e.g., x in %body(x: int) := e)
    // This is needed for properties like: forall i :: %body(i) == Unbox(bx, i)
    ghost var addedParams: set<string> := {};
    ghost var baseKeys := propertyVarMap.Keys;
    for i := 0 to |rawBindings|
      invariant addedParams == set bi, pi | 0 <= bi < i && 0 <= pi < |rawBindings[bi].params| :: rawBindings[bi].params[pi].name
      invariant propertyVarMap.Keys == baseKeys + addedParams
    {
      var rawBinding := rawBindings[i];
      for j := 0 to |rawBinding.params|
        invariant addedParams == (set bi, pi | 0 <= bi < i && 0 <= pi < |rawBindings[bi].params| :: rawBindings[bi].params[pi].name) + (set pi | 0 <= pi < j :: rawBinding.params[pi].name)
        invariant propertyVarMap.Keys == baseKeys + addedParams
      {
        var param := rawBinding.params[j];
        var paramType :- ResolveType(param.typ, ers.typeMap);
        var paramVar := new LocalVariable(param.name, false, paramType);
        propertyVarMap := propertyVarMap[param.name := paramVar];
        addedParams := addedParams + {param.name};
      }
    }
    
    // Prove addedParams == bindingParams (set equality)
    assert addedParams == bindingParams by {
      forall bi, pi | 0 <= bi < |rawBindings| && 0 <= pi < |rawBindings[bi].params|
        ensures rawBindings[bi].params[pi].name in bindingParams
      {
        assert rawBindings[bi] in rawBindings;
        assert rawBindings[bi].params[pi] in rawBindings[bi].params;
      }
    }
    
    // Final scope verification: propertyVarMap.Keys == rawPropertyScope
    // This is crucial for proving Raw.ClosureProperty.WellFormed
    assert baseKeys == varMap.Keys + {resultVar} + bindingNames;
    assert propertyVarMap.Keys == baseKeys + bindingParams;
    assert propertyVarMap.Keys == rawPropertyScope;

    // Resolve triggers (patterns that control quantifier instantiation)
    var resolvedTriggers :- ResolvePatterns(prop.triggers, ers, propertyVarMap);

    // Resolve property body expression
    var resolvedBody :- ResolveExpr(prop.body, ers, propertyVarMap);

    return Success(ClosureProperty(resolvedTriggers, resolvedBody));
  }
}
