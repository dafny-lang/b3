module DomainInstantiation {
  export
    provides Instantiate
    provides Ast, NamesAndLinearForms

  import opened Std.Wrappers
  import opened Basics
  import Raw = RawAst
  import opened Ast
  import NamesAndLinearForms

  method Instantiate(domain: Domain, selfTypeDecl: TypeDecl, typeArguments: seq<Type>) returns (instTypes: seq<TypeDecl>, instFunctions: seq<Function>, instAxioms: seq<Axiom>, instProcedures: seq<Procedure>)
    requires forall func <- domain.members.functions :: func.WellFormed()
    requires forall axiom <- domain.members.axioms :: axiom.WellFormed()
    requires Raw.LegalVariableName(selfTypeDecl.Name)
    requires |domain.params| == |typeArguments|
    requires NamedDecl.Distinct(domain.params + domain.members.types)
    ensures NamedDecl.Distinct(instTypes)
    ensures forall typ <- instTypes :: NamesAndLinearForms.HasPrefix(selfTypeDecl.Name, typ.Name)
    ensures forall axiom <- instAxioms :: axiom.WellFormed()
  {
    instTypes, instFunctions, instAxioms, instProcedures := [], [], [], [];
    var prefix := selfTypeDecl.Name + "..";
    var typesToBeInstantiated := domain.params + domain.members.types;

    for i := 0 to |typesToBeInstantiated|
      invariant |instTypes| == i
      invariant forall j :: 0 <= j < i ==> instTypes[j].Name == prefix + typesToBeInstantiated[j].Name
    {
      var typ := typesToBeInstantiated[i];
      var newName := prefix + typ.Name;
      var newType := new TypeDecl(newName);
      instTypes := instTypes + [newType];
    }
    // Prove the postconditions about "instTypes"
    forall i, j | 0 <= i < j < |instTypes|
      ensures instTypes[i].Name != instTypes[j].Name
    {
      Basics.CommonPrefixEquality(prefix, typesToBeInstantiated[i].Name, typesToBeInstantiated[j].Name);
    }
    forall i | 0 <= i < |instTypes|
      ensures NamesAndLinearForms.HasPrefix(selfTypeDecl.Name, instTypes[i].Name)
    {
      assert instTypes[i].Name == selfTypeDecl.Name + ".." + typesToBeInstantiated[i].Name;
      assert selfTypeDecl.Name + ".." <= selfTypeDecl.Name + ".." + typesToBeInstantiated[i].Name;
    }

    var tMap := map[domain.self := UserType(selfTypeDecl)];
    for i := 0 to |domain.params| {
      tMap := tMap[domain.params[i] := typeArguments[i]];
    }

    var fMap;
    instFunctions, fMap := InstantiateFunctions(domain.members.functions, tMap);

    var am;
    instAxioms, am := InstantiateAxioms(domain.members.axioms, tMap, fMap);
    FillInExplainedBy(domain.members.functions, instFunctions, am);

    instProcedures := InstantiateProcedures(domain.members.procedures, tMap, fMap);
  }

  function SubstituteType(typ: Type, tm: map<TypeDecl, Type>): Type {
    match typ
    case BoolType => BoolType
    case IntType => IntType
    case TagType => TagType
    case UserType(decl) => if decl in tm then tm[decl] else typ
  }

  method InstantiateFunctions(functions: seq<Function>, tMap: map<TypeDecl, Type>) returns (instFunctions: seq<Function>, fMap: map<Function, Function>)
    requires forall func <- functions :: func.WellFormed()
    ensures |functions| == |instFunctions|
    ensures fresh(instFunctions)
  {
    instFunctions, fMap := [], map[];

    // Functions have a .Tag field, which, if present, is a Function that is also being instantiated. Such a tag function
    // itself does not have another .Tag. Thus, we first instantiate the signature of functions without a tag. Then, we go
    // back to do the functions with tags. There's additional logic to get the new functions to be in the same order as the previous.
    for i := 0 to |functions|
      invariant forall j :: 0 <= j < i ==> functions[j].Tag == None ==> functions[j] in fMap
      invariant fresh(fMap.Values)
      invariant forall f <- fMap :: |f.Parameters| == |fMap[f].Parameters|
    {
      var func := functions[i];
      if func.Tag == None {
        var instFunc := InstantiateFunctionSignature(func, tMap, None);
        AboutExtendedMapValues(fMap, func, instFunc);
        fMap := fMap[func := instFunc];
      }
    }
    for i := 0 to |functions|
      invariant |instFunctions| == i
      invariant forall j :: 0 <= j < |functions| ==> functions[j].Tag == None ==> functions[j] in fMap
      invariant fresh(fMap.Values) && fresh(instFunctions)
      invariant forall f <- fMap :: |f.Parameters| == |fMap[f].Parameters|
      invariant forall j :: 0 <= j < i ==> |functions[j].Parameters| == |instFunctions[j].Parameters|
    {
      var func := functions[i];
      var instFunc;
      match func.Tag {
        case None =>
          // This function has no tag, so we already instantiated it in the previous loop
          instFunc := fMap[func];
          assert instFunc in fMap.Values;
        case Some(tagger) =>
          expect tagger in fMap; // we expect all tagger functions also to be included in the list "functions"
          var instTagger := fMap[tagger];
          instFunc := InstantiateFunctionSignature(func, tMap, Some(instTagger));
      }
      assert fresh(instFunc);
      instFunctions := instFunctions + [instFunc];
      AboutExtendedMapValues(fMap, func, instFunc);
      fMap := fMap[func := instFunc];
    }

    // Once more, go through the functions, this time to fill in the function definitions.
    for i := 0 to |functions|
    {
      var func := functions[i];
      var instFunc := instFunctions[i];
      match func.Definition
      case None =>
        instFunc.Definition := None;
      case Some(def) =>
        forall i, j | 0 <= i < j < |func.Parameters|
          ensures func.Parameters[i] != func.Parameters[j]
        {
          assert func in functions;
          assert func.SignatureWellFormed();
          assert func.Parameters[i].name != func.Parameters[j].name;
        }
        var vMap := map i | 0 <= i < |func.Parameters| :: func.Parameters[i] := instFunc.Parameters[i];
        var instWhen := SubstituteExpressionList(def.when, tMap, fMap, vMap);
        var instBody := SubstituteExpression(def.body, tMap, fMap, vMap);
        instFunc.Definition := Some(FunctionDefinition(instWhen, instBody));
    }
  }

  method InstantiateFunctionSignature(func: Function, tm: map<TypeDecl, Type>, instTagger: Option<Function>) returns (instFunc: Function)
    requires func.Tag.Some? <==> instTagger.Some?
    ensures fresh(instFunc)
    ensures |func.Parameters| == |instFunc.Parameters|

  {
    var parameters: seq<FParameter> := [];
    for i := 0 to |func.Parameters|
      invariant |parameters| == i
    {
      var p := func.Parameters[i];
      var newParameter := new FParameter(p.name, p.injective, SubstituteType(p.typ, tm));
      parameters := parameters + [newParameter];
    }
    var resultType := SubstituteType(func.ResultType, tm);
    instFunc := new Function(func.Name, parameters, resultType, instTagger);
  }

  method FillInExplainedBy(functions: seq<Function>, instFunctions: seq<Function>, am: map<Axiom, Axiom>)
    requires |functions| == |instFunctions|
    requires forall f0 <- functions, f1 <- instFunctions :: f0 != f1
    modifies instFunctions
  {
    for i := 0 to |instFunctions|
      invariant forall func <- functions :: unchanged(func)
    {
      var func := functions[i];
      var instFunc := instFunctions[i];
      assert func in functions && instFunc in instFunctions && instFunc !in functions;
      var axioms := func.ExplainedBy;
      expect forall axiom <- axioms :: axiom in am;
      instFunc.ExplainedBy := seq(|axioms|, j requires 0 <= j < |axioms| => am[axioms[j]]);
    }    
  }

  method InstantiateAxioms(axioms: seq<Axiom>, tMap: map<TypeDecl, Type>, fMap: map<Function, Function>) returns (instAxioms: seq<Axiom>, am: map<Axiom, Axiom>)
    requires forall axiom <- axioms :: axiom.WellFormed()
    ensures forall axiom <- instAxioms :: axiom.WellFormed()
  {
    instAxioms, am := [], map[];
    for i := 0 to |axioms|
      invariant |instAxioms| == i
      invariant forall axiom <- instAxioms :: axiom.WellFormed()
    {
      var axiom := axioms[i];
      assert axiom in axioms;
      expect forall explain <- axiom.Explains :: explain in fMap;
      var instExplains := seq(|axiom.Explains|,
        i requires 0 <= i < |axiom.Explains| => fMap[axiom.Explains[i]]);
      var e := SubstituteExpression(axiom.Expr, tMap, fMap, map[]);
      var instAxiom := new Axiom(instExplains, e);
      assert instAxiom.WellFormed();
      am := am[axiom := instAxiom];
      instAxioms := instAxioms + [instAxiom];
    }
  }

  method SubstituteExpressionList(exprs: seq<Expr>, tm: map<TypeDecl, Type>, fm: map<Function, Function>, vm: map<Variable, Variable>) returns (instExprs: seq<Expr>)
    requires forall expr <- exprs :: expr.WellFormed()
    ensures |exprs| == |instExprs|
    ensures forall expr <- instExprs :: expr.WellFormed()
  {
    instExprs := [];
    for i := 0 to |exprs|
      invariant |instExprs| == i
      invariant forall expr <- instExprs :: expr.WellFormed()
    {
      var expr := exprs[i];
      var instExpr := SubstituteExpression(expr, tm, fm, vm);
      instExprs := instExprs + [instExpr];
    }
  }

  method SubstituteExpression(expr: Expr, tm: map<TypeDecl, Type>, fm: map<Function, Function>, vm: map<Variable, Variable>) returns (instExpr: Expr)
    requires expr.WellFormed()
    ensures instExpr.WellFormed()
    decreases expr
  {
    match expr
    case BLiteral(value) =>
      instExpr := BLiteral(value);
    case ILiteral(value) =>
      instExpr := ILiteral(value);
    case CustomLiteral(s, typ) =>
      var ctyp := SubstituteType(typ, tm);
      // TODO: the following condition should be checked by disallowing custom literals from ever having a type-parameter type
      expect ctyp != BoolType && ctyp != IntType, "unchecked condition: domain instantiation should not allow custom-literal types to become bool or int";
      instExpr := CustomLiteral(s, ctyp);
    case IdExpr(v) =>
      expect v in vm;
      instExpr := IdExpr(vm[v]);
    case OperatorExpr(op, args) =>
      var instArgs := SubstituteExpressionList(args, tm, fm, vm);
      instExpr := OperatorExpr(op, instArgs);
    case FunctionCallExpr(func, args) =>
      expect func in fm;
      var actualFunc := fm[func];
      expect |func.Parameters| == |actualFunc.Parameters|;
      var instArgs := SubstituteExpressionList(args, tm, fm, vm);
      instExpr := FunctionCallExpr(actualFunc, instArgs);
    case LabeledExpr(lbl, body) =>
      var newLabel := new Label(lbl.Name);
      var labeledBody := SubstituteExpression(body, tm, fm, vm);
      instExpr := LabeledExpr(newLabel, labeledBody);
    case LetExpr(v, rhs, body) =>
      var instRhs := SubstituteExpression(rhs, tm, fm, vm);
      var instVar := v.Create(v.name, SubstituteType(v.typ, tm));
      var bodyMap := vm[v := instVar];
      var instBody := SubstituteExpression(body, tm, fm, bodyMap);
      instExpr := LetExpr(instVar, instRhs, instBody);
    case QuantifierExpr(univ, vv, patterns, body) =>
      var instVars := [];
      var bindingMap := vm;
      for i := 0 to |vv|
        invariant |instVars| == i
      {
        var oldVar: Variable := vv[i];
        var instVar := oldVar.Create(oldVar.name, SubstituteType(oldVar.typ, tm));
        instVars := instVars + [instVar];
        bindingMap := bindingMap[oldVar := instVar];
      }
      var instPatterns := SubstitutePatternList(patterns, tm, fm, bindingMap);
      var instBody := SubstituteExpression(body, tm, fm, bindingMap);
      instExpr := QuantifierExpr(univ, instVars, instPatterns, instBody);
    case ClosureExpr(closureBindings, resultVar, resultType, properties) =>
      var instBindings := [];
      for i := 0 to |closureBindings|
        invariant |instBindings| == i
        invariant forall b: ClosureBinding <- instBindings :: b.WellFormed()
      {
        var binding := closureBindings[i];
        assert binding in closureBindings;
        var instParams := [];
        for j := 0 to |binding.params|
          invariant |instParams| == j
        {
          var param := binding.params[j];
          instParams := instParams + [(param.0, SubstituteType(param.1, tm))];
        }
        var rhs := SubstituteExpression(binding.rhs, tm, fm, vm);
        instBindings := instBindings + [ClosureBinding(binding.name, instParams, rhs)];
      }
      var instProperties := [];
      for i := 0 to |properties|
        invariant |instProperties| == i
        invariant forall p: ClosureProperty <- instProperties :: p.WellFormed()
      {
        var prop := properties[i];
        assert prop in properties;
        var instTriggers := SubstitutePatternList(prop.triggers, tm, fm, vm);
        var instBody := SubstituteExpression(prop.body, tm, fm, vm);
        instProperties := instProperties + [ClosureProperty(instTriggers, instBody)];
      }
      instExpr := ClosureExpr(instBindings, resultVar, SubstituteType(resultType, tm), instProperties);
  }

  method SubstitutePattern(pattern: Pattern, tm: map<TypeDecl, Type>, fm: map<Function, Function>, vm: map<Variable, Variable>) returns (instPattern: Pattern)
    requires pattern.WellFormed()
    ensures instPattern.WellFormed()
  {
    var instExprsResult := SubstituteExpressionList(pattern.exprs, tm, fm, vm);
    instPattern := Pattern(instExprsResult);
  }

  method SubstitutePatternList(patterns: seq<Pattern>, tm: map<TypeDecl, Type>, fm: map<Function, Function>, vm: map<Variable, Variable>) returns (instPatterns: seq<Pattern>)
    requires forall pattern <- patterns :: pattern.WellFormed()
    ensures |patterns| == |instPatterns|
    ensures forall pattern <- instPatterns :: pattern.WellFormed()
  {
    instPatterns := [];
    for i := 0 to |patterns|
      invariant |instPatterns| == i
      invariant forall pattern <- instPatterns :: pattern.WellFormed()
    {
      var pattern := patterns[i];
      var instPattern := SubstitutePattern(pattern, tm, fm, vm);
      instPatterns := instPatterns + [instPattern];
    }
  }

  method InstantiateProcedures(procedures: seq<Procedure>, tm: map<TypeDecl, Type>, fm: map<Function, Function>) returns (instProcedures: seq<Procedure>)
  {
    instProcedures := [];
    // TODO
  }
}
