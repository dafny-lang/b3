module Resolver {
  export
    provides Resolve
    provides Wrappers, Raw, Ast

  import opened Std.Wrappers
  import opened Basics
  import opened Types
  import Raw = RawAst
  import opened Ast
  import Printer
  import FunctionDesugaring
  import opened NamesAndLinearForms
  import opened TypeResolver
  import opened DomainResolver
  import opened StmtResolver
  import opened ExprResolver
  import DomainInstantiation

  ghost predicate GoodTypeMap(b3: Raw.Program, typeMap: map<string, TypeDecl>, generatedTypes: set<string> := {}) {
    forall typename :: b3.IsType(typename) || typename in generatedTypes <==> typename in BuiltInTypes || typename in typeMap
  }

  method Resolve(b3: Raw.Program, typeParameters: seq<TypeDecl>) returns (r: Result<Ast.Program, string>, ghost generatedTypes: set<string>)
    requires forall param <- typeParameters :: Raw.LegalVariableName(param.Name)
    requires NamedDecl.Distinct(typeParameters)
    requires b3.signatureTypes == set param <- typeParameters :: param.Name
    ensures r.Success? ==>
      && b3.WellFormed(generatedTypes)
      && r.value.WellFormed()
      && NamedDecl.Distinct(typeParameters + r.value.types)
    decreases b3
  {
    generatedTypes := {};
    var domainMap, domains :- ResolveAllDomains(b3);

    var typeMap, types :- ResolveAllTypes(b3, typeParameters);
    assert NamedDecl.Distinct(typeParameters + types);
    forall typ <- b3.types
      ensures Raw.LegalVariableName(typ.name)
    {
      assert typ.name in typeMap;
      assert typeMap[typ.name] in types by {
        LinearFormL2R(typ.name, typeMap, typeParameters + types);
      }
    }
    ghost var typeParameterNames := set param <- typeParameters :: param.Name;

    // Note, by resolving all domain-instantiation RHSs before actually instantiating the domains, we avoid the possibility
    // of a domain-instantiation RHS referring to a type that is defined in a domain that is being instantiated. That is,
    // we avoid ordering dependencies among domains. With more advanced uses of domains, it would be good to extend the
    // language to allow some such dependencies.
    var resolvedInstantiations :- ResolveDomainInstantiations(b3, domainMap, typeMap);
    var instTypes, instFunctions, instAxioms, instProcedures := InstantiateDomains(resolvedInstantiations);
    typeMap, generatedTypes := AddGeneratedTypes(b3, typeMap, instTypes);

    var taggerMap, taggerFunctions :- ResolveAllTaggers(b3, typeMap, generatedTypes);
    ConsequencesOfTagResolution(taggerMap, taggerFunctions);

    var functionMap, functions, generatedAxioms :- ResolveAllFunctions(b3, typeMap, generatedTypes, taggerMap);

    var ers := ExprResolverState(b3, typeMap, generatedTypes, taggerMap + functionMap);
    assert ers.Valid();
    assert fresh(ers.functionMap.Values) by {
      assert ers.functionMap.Values == taggerMap.Values + functionMap.Values;
      assert fresh(taggerMap.Values) by {
        LinearFormValues(taggerMap, taggerFunctions);
      }
      assert fresh(functionMap.Values) by {
        LinearFormValues(functionMap, functions);
      }
    }
    var axioms :- ResolveAllAxioms(ers);

    var procMap, procedures :- ResolveAllProcedures(ers);

    var r3 := Program(domains,
      types + instTypes,
      taggerFunctions + functions + instFunctions,
      generatedAxioms + axioms + instAxioms,
      procedures + instProcedures);
    assert NamedDecl.Distinct(typeParameters + (types + instTypes)) by {
      assert typeParameters + (types + instTypes) == (typeParameters + types) + instTypes;
      assert NamedDecl.Distinct(typeParameters + types);
      assert NamedDecl.Distinct(instTypes);
      forall typ: TypeDecl <- typeParameters + types
        ensures !Raw.HasDoubleDot(typ.Name)
      {
        assert Raw.LegalVariableName(typ.Name);
        reveal Raw.LegalVariableName;
      }
      assert forall typ <- instTypes :: Raw.HasDoubleDot(typ.Name);
    }
    assert NamedDecl.Distinct(types + instTypes) by {
      assert forall i :: 0 <= i < |types + instTypes| ==> (types + instTypes)[i] == (typeParameters + (types + instTypes))[|typeParameters| + i];
    }
    DistinctConcat(taggerMap, taggerFunctions, functionMap, functions);
    
    assert NamedDecl.Distinct(taggerFunctions + functions + instFunctions) by {
      var ff: seq<Function> := taggerFunctions + functions;
      var fff: seq<Function> := taggerFunctions + functions + instFunctions;
      assert NamedDecl.Distinct(ff); // by the call to DistinctConcat above
      assume {:axiom} NamedDecl.Distinct(instFunctions); // TODO
      assume {:axiom} forall f0 <- ff, f1 <- instFunctions :: f0.Name != f1.Name; // TODO
    }
    assume {:axiom} forall func <- instFunctions :: func.WellFormed();

    assert NamedDecl.Distinct(procedures + instProcedures) by {
      assert NamedDecl.Distinct(procedures);
      assume {:axiom} NamedDecl.Distinct(instProcedures); // TODO
      assume {:axiom} forall p0 <- procedures, p1 <- instProcedures :: p0.Name != p1.Name; // TODO
    }
    assume {:axiom} forall proc <- instProcedures :: proc.WellFormed();

    return Success(r3), generatedTypes;
  }

  method ResolveAllDomains(b3: Raw.Program) returns (r: Result<map<string, Domain>, string>, domains: seq<Domain>)
    ensures r.Success? ==> var domainMap := r.value;
      && LinearForm(domainMap, domains)
      && (forall domainName <- domainMap :: var domain := domainMap[domainName];
        && domain.WellFormed()
        && (forall func <- domain.members.functions :: func.SignatureWellFormed()))
    decreases b3, 0
  {
    var domainMap: map<string, Domain> := map[];
    domains := [];
    for n := 0 to |b3.domains|
      // domainMap maps domains seen so far to distinct domain-declaration objects
      invariant domainMap.Keys == set domain <- b3.domains[..n] :: domain.name
      // domainMap organizes domain-declaration objects correctly according to their names
      invariant forall name <- domainMap :: domainMap[name].self.Name == name
      // domains seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.domains[i] != b3.domains[j]
      // connection between domainMap and domains
      invariant LinearForm(domainMap, domains)
      // domains are well-formed
      invariant forall domainName <- domainMap :: var domain := domainMap[domainName];
        && domain.WellFormed()
        && (forall func <- domain.members.functions :: func.SignatureWellFormed())
    {
      var domain := b3.domains[n];

      var name := domain.name;
      // The following condition is established by the parser:
      expect domain.members.signatureTypes == {name} + (set parameterTypeName <- domain.params), "internal error: incorrectly formed Domain value";
      if !Raw.LegalVariableName(name) {
        return Failure("domain name is not a legal name: '" + name + "'"), domains;
      } else if name in domainMap {
        return Failure("duplicate domain name: " + name), domains;
      }
      var self := new TypeDecl(name);
      var typesForUseInDomainBody: seq<TypeDecl> := [self];

      var params := [];
      for i := 0 to |domain.params|
        invariant |typesForUseInDomainBody| == 1 + i
        invariant typesForUseInDomainBody == [self] + params
        invariant forall typ <- typesForUseInDomainBody :: Raw.LegalVariableName(typ.Name)
        invariant forall j :: 0 <= j < 1 + i ==> typesForUseInDomainBody[j].Name == if j == 0 then name else domain.params[j - 1]
        invariant forall i, j :: 0 <= i < j < |typesForUseInDomainBody| ==> typesForUseInDomainBody[i].Name != typesForUseInDomainBody[j].Name
      {
        var typeParamName := domain.params[i];
        if !Raw.LegalVariableName(typeParamName) {
          return Failure("domain type parameter is not a legal name: '" + typeParamName + "'"), domains;
        } else if name == typeParamName {
          return Failure("domain type parameter is not allowed to have the same name of the domain itself: '" + typeParamName + "'"), domains;
        } else if exists priorTypeParam: TypeDecl <- params :: priorTypeParam.Name == typeParamName {
          return Failure("duplicate domain type parameter name: '" + typeParamName + "'"), domains;
        }
        var typeParam := new TypeDecl(typeParamName);
        params := params + [typeParam];
        typesForUseInDomainBody := typesForUseInDomainBody + [typeParam];
      }

      assert domain.members.signatureTypes == set param: TypeDecl <- typesForUseInDomainBody :: param.Name by {
        var names := seq(|typesForUseInDomainBody|, i requires 0 <= i < |typesForUseInDomainBody| => typesForUseInDomainBody[i].Name);
        calc {
          domain.members.signatureTypes;
          // by "expect" above
          ({name} + set parameterTypeName <- domain.params);
          set parameterTypeName <- [name] + domain.params;
          { assert [name] + domain.params == names; }
          set parameterTypeName <- names;
        }
      }
      var resolvedMembers, _ :- Resolve(domain.members, typesForUseInDomainBody);
      assert NamedDecl.Distinct(typesForUseInDomainBody + resolvedMembers.types);

      var decl := Domain(self, params, resolvedMembers);
      assert decl.WellFormed();
      NewNamePreservesLinearForm(name, decl, domainMap, domains);
      domainMap := domainMap[name := decl];
      domains := domains + [decl];
    }
    return Success(domainMap), domains;
  }

  method ResolveAllTypes(b3: Raw.Program, typeParameters: seq<TypeDecl>) returns (r: Result<map<string, TypeDecl>, string>, types: seq<TypeDecl>)
    requires forall param <- typeParameters :: Raw.LegalVariableName(param.Name)
    requires NamedDecl.Distinct(typeParameters)
    ensures r.Success? ==> var typeMap := r.value;
      var typeParameterNames := set param <- typeParameters :: param.Name;
      // raw types were well-formed
      && typeMap.Keys == typeParameterNames + (set typeDecl: Raw.TypeDecl <- b3.types :: typeDecl.name)
      && NameAlignment(typeMap)
      && (forall typeDecl <- b3.types :: typeDecl.name !in BuiltInTypes && typeDecl.name !in typeParameterNames)
      && (forall i, j :: 0 <= i < j < |b3.types| ==> b3.types[i].name != b3.types[j].name)
      // resolved type declarations have legal, distinct names
      && NamedDecl.Distinct(typeParameters + types)
      && (forall typ <- types :: Raw.LegalVariableName(typ.Name))
      // typeMap.Keys/types correspondence
      && LinearForm(r.value, typeParameters + types)
  {
    var typeMap: map<string, TypeDecl> := map[];
    types := [];

    // Add the type parameters to the typeMap
    for n := 0 to |typeParameters|
      invariant typeMap.Keys == set param: TypeDecl <- typeParameters[..n] :: param.Name
      invariant NameAlignment(typeMap)
      invariant NamedDecl.Distinct(typeParameters[..n])
      invariant forall typ: TypeDecl <- typeParameters[..n] :: Raw.LegalVariableName(typ.Name)
      invariant LinearForm(typeMap, typeParameters[..n])
    {
      var param := typeParameters[n];
      var name := param.Name;
      assert name !in typeMap;
      if !Raw.LegalVariableName(name) {
        return Result<map<string, TypeDecl>, string>.Failure("type parameter is not a legal name: " + name), types;
      } else if name in BuiltInTypes {
        return Result<map<string, TypeDecl>, string>.Failure("type parameter is not allowed to have the name of a built-in type: " + name), types;
      }
      if name in BuiltInTypes {
           return Result<map<string, TypeDecl>, string>.Failure("type parameter is not allowed to have the name of a built-in type: " + name), types;
      }
      NewNamePreservesLinearFormAndIsUnique(name, param, typeMap, typeParameters[..n]);
      typeMap := typeMap[name := param];
    }
    assert typeParameters == typeParameters[..|typeParameters|];
    ghost var typeParameterNames := set param <- typeParameters :: param.Name;
    assert typeMap.Keys == typeParameterNames;

    // Add the types declared in the program/domain
    for n := 0 to |b3.types|
      // typeMap maps type parameters and user-defined types seen so far to distinct type-declaration objects
      invariant typeMap.Keys == typeParameterNames + set typeDecl <- b3.types[..n] :: typeDecl.name
      // typeMap organizes type-declaration objects correctly according to their names
      invariant NameAlignment(typeMap)
      // no user-defined type seen so far uses the name of a built-in type
      invariant forall typeDecl <- b3.types[..n] :: typeDecl.name !in BuiltInTypes && typeDecl.name !in typeParameterNames
      // user-defined types seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.types[i].name != b3.types[j].name
      // resolved type declarations have distinct names and do not contain a double dot
      invariant NamedDecl.Distinct(typeParameters + types)
      invariant forall typ <- types :: Raw.LegalVariableName(typ.Name)
      // typeMap.Keys/types correspondence
      invariant LinearForm(typeMap, typeParameters + types)
    {
      var name := b3.types[n].name;
      if !Raw.LegalVariableName(name) {
        return Result<map<string, TypeDecl>, string>.Failure("user-defined type is not a legal name: " + name), types;
      } else if name in BuiltInTypes {
        return Result<map<string, TypeDecl>, string>.Failure("user-defined type is not allowed to have the name of a built-in type: " + name), types;
      } else if name in typeMap {
        return Failure("duplicate type name: " + name), types;
      }
      var decl := new TypeDecl(name);
      assert (typeParameters + types) + [decl] == typeParameters + (types + [decl]);
      NewNamePreservesLinearFormAndIsUnique(name, decl, typeMap, typeParameters + types);
      typeMap := typeMap[name := decl];
      types := types + [decl];
    }

    return Success(typeMap), types;
  }

  method AddGeneratedTypes(ghost b3: Raw.Program, typeMap: map<string, TypeDecl>, instTypes: seq<TypeDecl>) returns (newTypeMap: map<string, TypeDecl>, generatedTypes: set<string>)
    requires GoodTypeMap(b3, typeMap)
    ensures GoodTypeMap(b3, newTypeMap, generatedTypes)
  {
    newTypeMap, generatedTypes := typeMap, {};
    for i := 0 to |instTypes|
      invariant GoodTypeMap(b3, newTypeMap, generatedTypes)
    {
      var typ := instTypes[i];
      newTypeMap := newTypeMap[typ.Name := typ];
      generatedTypes := generatedTypes + {typ.Name};
    }
  }

  method ResolveAllTaggers(b3: Raw.Program, typeMap: map<string, TypeDecl>, ghost generatedTypes: set<string>) returns (r: Result<map<string, Function>, string>, taggerFunctions: seq<Function>)
    requires GoodTypeMap(b3, typeMap, generatedTypes)
    ensures r.Success? ==>
      // raw taggers were well-formed
      && (forall i, j :: 0 <= i < j < |b3.taggers| ==> b3.taggers[i].name != b3.taggers[j].name)
      && (forall tagger <- b3.taggers :: tagger.WellFormed(b3))
    ensures r.Success? ==> var taggerMap: map<string, Function> := r.value;
      && NameAlignment(taggerMap)
      && taggerMap.Keys == (set tagger <- b3.taggers :: tagger.name)
      && LinearForm(taggerMap, taggerFunctions)
    ensures r.Success? ==>
      && NamedDecl.Distinct(taggerFunctions)
      && fresh(taggerFunctions)
      && (forall tagger <- taggerFunctions :: tagger.WellFormedAsTagger())
  {
    var taggerMap: map<string, Function> := map[];
    taggerFunctions := [];
    for n := 0 to |b3.taggers|
      // taggerMap maps the user-defined taggers seen so far to distinct and fresh tagger-declaration objects
      invariant taggerMap.Keys == set tagger <- b3.taggers[..n] :: tagger.name
      invariant fresh(taggerFunctions)
      // taggerMap organizes tagger-declaration objects correctly according to their names
      invariant NameAlignment(taggerMap)
      // taggers seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.taggers[i].name != b3.taggers[j].name
      // taggers seen so far are well-formed
      invariant forall tagger <- b3.taggers[..n] :: tagger.WellFormed(b3)
      invariant forall tagger <- taggerFunctions :: tagger.WellFormedAsTagger()
      // resolved tagger functions have distinct names
      invariant forall i, j :: 0 <= i < j < |taggerFunctions| ==> taggerFunctions[i].Name != taggerFunctions[j].Name
      // taggerFunctions is a linear order of the tagger functions
      invariant LinearForm(taggerMap, taggerFunctions)
    {
      var tagger := b3.taggers[n];
      var name := tagger.name;
      if name in taggerMap {
        return Failure("duplicate tagger name: " + name), taggerFunctions;
      }
      var typ :- ResolveType(tagger.typ, typeMap);

      Raw.SurelyLegalVariableName("subject");
      var parameter := new FParameter("subject", false, typ);
      assert Raw.LegalVariableName("subject");
      assert parameter.WellFormed();
      var rTagger := new Function(name, [parameter], TagType, None);
      NewNamePreservesLinearFormAndIsUnique(name, rTagger, taggerMap, taggerFunctions);
      taggerMap := taggerMap[name := rTagger];
      assert forall tagger <- taggerFunctions :: tagger.WellFormedAsTagger();
      assert rTagger.WellFormedAsTagger() by {
        assert rTagger.WellFormed();
        assert |rTagger.Parameters| == 1 && rTagger.ResultType == TagType;
      }
      taggerFunctions := taggerFunctions + [rTagger];
      assert forall tagger <- taggerFunctions :: tagger.WellFormedAsTagger();
    }
    return Success(taggerMap), taggerFunctions;
  }

  lemma ConsequencesOfTagResolution(taggerMap: map<string, Function>, taggerFunctions: seq<Function>)
    requires LinearForm(taggerMap, taggerFunctions)
    requires forall f <- taggerFunctions :: f.WellFormedAsTagger()
    ensures forall f <- taggerFunctions :: f.WellFormed()
    ensures forall name <- taggerMap :: taggerMap[name].WellFormedAsTagger()
  {
    assert forall f: Function :: f.WellFormedAsTagger() ==> f.WellFormed();

    forall taggerName <- taggerMap
      ensures taggerMap[taggerName].WellFormedAsTagger()
    {
      LinearFormL2R(taggerName, taggerMap, taggerFunctions);
    }
  }

  method ResolveAllFunctions(b3: Raw.Program, typeMap: map<string, TypeDecl>, ghost generatedTypes: set<string>, taggerMap: map<string, Function>)
      returns (r: Result<map<string, Function>, string>, functions: seq<Function>, axioms: seq<Axiom>)
    requires GoodTypeMap(b3, typeMap, generatedTypes)
    requires NameAlignment(taggerMap)
    requires forall taggerName <- taggerMap :: taggerMap[taggerName].WellFormedAsTagger()
    ensures r.Success? ==>
      // raw functions had distinct names and were well-formed
      && (forall i, j :: 0 <= i < j < |b3.functions| ==> b3.functions[i].name != b3.functions[j].name)
      && (forall func <- b3.functions :: func.WellFormed(b3, generatedTypes))
    ensures r.Success? ==> var functionMap := r.value;
      && taggerMap.Keys !! functionMap.Keys
      && NameAlignment(functionMap)
      && LinearForm(functionMap, functions)
/* raw/resolved CORRESPONDENCE property:
      && (forall rawFunction <- b3.functions ::
            && rawFunction.name in functionMap
            && var func := functionMap[rawFunction.name];
            && |rawFunction.parameters| == |func.Parameters|
         )
*/
    ensures r.Success? ==>
      // the resolved functions returned have distinct names, are freshly allocated, and are well-formed
      && NamedDecl.Distinct(functions)
      && fresh(functions) && fresh(axioms)
      && (forall func <- functions :: func.WellFormed())
      && (forall axiom <- axioms :: axiom.WellFormed())
  {
    var functionMap: map<string, Function> := map[];
    functions, axioms := [], [];
    for n := 0 to |b3.functions|
      // properties of the raw functions seen so far
      invariant forall i, j :: 0 <= i < j < n ==> b3.functions[i].name != b3.functions[j].name
      invariant forall func <- b3.functions[..n] :: func.name in functionMap
      invariant forall func <- b3.functions[..n] :: func.SignatureWellFormed(b3, generatedTypes) && functionMap[func.name].SignatureCorrespondence(func)
      // properties of functionMap
      invariant taggerMap.Keys !! functionMap.Keys
      invariant NameAlignment(functionMap)
      invariant LinearForm(functionMap, functions)
      // properties of functions and axioms
      invariant NamedDecl.Distinct(functions)
      invariant fresh(functions) && fresh(axioms)
      invariant forall func <- functions :: func.WellFormed()
      invariant forall axiom <- axioms :: axiom.WellFormed()
    {
      var func := b3.functions[n];
      var name := func.name;
      var _ :- CheckNameDuplication(name, taggerMap, functionMap, "");
      var rFunc :- ResolveFunctionSignature(func, b3, typeMap, generatedTypes, taggerMap);
      NewNamePreservesLinearFormAndIsUnique(name, rFunc, functionMap, functions);
      functionMap := functionMap[name := rFunc];
      functions := functions + [rFunc];

      // desugar injective parameters and tags into additional functions and axioms
      var generatedFunctions, generatedAxioms := FunctionDesugaring.CreateInverseAndTagFunctions(rFunc);
      ghost var prevFunctionMap := functionMap;
      for i := 0 to |generatedFunctions|
        invariant prevFunctionMap.Keys <= functionMap.Keys
        invariant forall prevFunctionName <- prevFunctionMap :: prevFunctionMap[prevFunctionName] == functionMap[prevFunctionName]
        invariant taggerMap.Keys !! functionMap.Keys
        invariant NameAlignment(functionMap)
        invariant LinearForm(functionMap, functions)
        invariant NamedDecl.Distinct(functions)
        invariant fresh(functions)
        invariant forall func: Function <- generatedFunctions :: func.WellFormed()
        invariant forall func <- functions :: func.WellFormed()
      {
        var generatedFunc := generatedFunctions[i];
        var name := generatedFunc.Name;
        var _ :- CheckNameDuplication(name, taggerMap, functionMap, "generated ");
        NewNamePreservesLinearFormAndIsUnique(name, generatedFunc, functionMap, functions);
        functionMap := functionMap[name := generatedFunc];
        functions := functions + [generatedFunc];
      }
      axioms := axioms + generatedAxioms;
    }

    var ers := ExprResolverState(b3, typeMap, generatedTypes, taggerMap + functionMap);
    for n := 0 to |b3.functions|
      invariant forall func <- b3.functions :: func.SignatureWellFormed(b3, generatedTypes) && functionMap[func.name].SignatureCorrespondence(func)
      invariant forall func <- b3.functions[..n] :: func.WellFormed(b3, generatedTypes) && functionMap[func.name].WellFormed()
      invariant forall func <- functions :: func.WellFormed()
    {
      var func := b3.functions[n];
      var rFunc := functionMap[func.name];
      assert rFunc in functions by {
        LinearFormL2R(func.name, functionMap, functions);
      }
      var _ :- ResolveFunctionDefinition(func, rFunc, ers);
    }

    // Generate definition axioms for all (user-defined and generated) functions
    for n := 0 to |functions|
      invariant forall func <- functions :: func.WellFormed()
      invariant forall axiom <- axioms :: axiom.WellFormed()
      invariant fresh(axioms)
    {
      var func := functions[n];
      if func.Definition.Some? {
        var axiom := FunctionDesugaring.DefinitionAxiom(func);
        axioms := axioms + [axiom];
      }
    }

    return Success(functionMap), functions, axioms;
  }

  method CheckNameDuplication(name: string, taggerMap: map<string, Function>, functionMap: map<string, Function>, prefix: string) returns (r: Result<(), string>)
    ensures r.Success? ==> name !in taggerMap && name !in functionMap
  {
    if name in taggerMap.Keys {
      return Failure(prefix + "function has the same name as a tagger" + name);
    } else if name in functionMap.Keys {
      return Failure(prefix + "function has the same name as a previously defined function: " + name);
    }
    return Success(());
  }

  method ResolveFunctionSignature(func: Raw.Function, b3: Raw.Program, typeMap: map<string, TypeDecl>, ghost generatedTypes: set<string>, taggerMap: map<string, Function>) returns (r: Result<Function, string>)
    requires GoodTypeMap(b3, typeMap, generatedTypes)
    requires forall taggerName <- taggerMap :: taggerMap[taggerName].Name == taggerName && taggerMap[taggerName].WellFormedAsTagger()
    ensures r.Success? ==> func.SignatureWellFormed(b3, generatedTypes)
    ensures r.Success? ==> fresh(r.value) && r.value.SignatureCorrespondence(func) && r.value.WellFormed()
  {
    var paramMap: map<string, Variable> := map[];
    var formals: seq<FParameter> := [];
    for n := 0 to |func.parameters|
      invariant forall p <- func.parameters[..n] :: Raw.LegalVariableName(p.name) && (b3.IsType(p.typ) || p.typ in generatedTypes)
      invariant forall i, j :: 0 <= i < j < n ==> func.parameters[i].name != func.parameters[j].name
      invariant paramMap.Keys == (set p <- func.parameters[..n] :: p.name)
      invariant |formals| == n
      invariant forall i :: 0 <= i < n ==> formals[i] == paramMap[func.parameters[i].name]
      invariant forall i :: 0 <= i < n ==> formals[i].name == func.parameters[i].name
      invariant forall i :: 0 <= i < n ==> formals[i].injective == func.parameters[i].injective
    {
      var p := func.parameters[n];
      if !Raw.LegalVariableName(p.name) {
        return Failure("illegal parameter name: " + p.name);
      }
      if p.name in paramMap {
        return Failure("duplicate parameter name: " + p.name);
      }
      var typ :- ResolveType(p.typ, typeMap);

      var formal: FParameter := new FParameter(p.name, p.injective, typ);
      paramMap := paramMap[p.name := formal];
      formals := formals + [formal];
    }

    var resultType :- ResolveType(func.resultType, typeMap);

    var maybeTag := None;
    if func.tag.Some? {
      var tagName := func.tag.value;
      if tagName !in taggerMap {
        return Failure("use of undeclared tagger: " + tagName);
      }
      var tag := taggerMap[tagName];
      var taggerForType := tag.Parameters[0].typ;
      if taggerForType != resultType {
        var msg := "tagger '" + tagName + "' is for type '" + taggerForType.ToString() + "' and must agree with function result type '" + resultType.ToString() + "'";
        return Result<Function, string>.Failure(msg);
      }
      maybeTag := Some(tag);
    }

    var rfunc := new Function(func.name, formals, resultType, maybeTag);
    return Success(rfunc);
  }

  method ResolveFunctionDefinition(func: Raw.Function, rfunc: Function, ers: ExprResolverState) returns (r: Result<(), string>)
    requires func.SignatureWellFormed(ers.b3, ers.generatedTypes) && rfunc.SignatureCorrespondence(func) && ers.Valid()
    requires rfunc.WellFormed()
    modifies rfunc`Definition
    ensures r.Success? ==> func.WellFormed(ers.b3, ers.generatedTypes) && rfunc.WellFormed()
  {
    if func.definition == None {
      rfunc.Definition := None;
      return Success(());
    }

    var formals := rfunc.Parameters;
    var n := |formals|;
    assert forall formal: FParameter <- formals :: Raw.LegalVariableName(formal.name);
    assert forall i, j :: 0 <= i < j < n ==> formals[i].name != formals[j].name;
    var paramMap := map formal <- rfunc.Parameters :: formal.name := formal;

    assert n == |func.parameters|;
    assert forall i :: 0 <= i < n ==> formals[i].name == func.parameters[i].name;

    var bodyScope := set p <- func.parameters :: p.name;
    var whenScope := bodyScope;

    var whenVariables := MapProject(paramMap, whenScope);
    assert whenVariables.Keys == whenScope;
    var when :- ResolveExprList(func.definition.value.when, ers, whenVariables);

    var bodyVariables := MapProject(paramMap, bodyScope);
    assert bodyVariables.Keys == bodyScope;
    var body :- ResolveExpr(func.definition.value.body, ers, bodyVariables);

    rfunc.Definition := Some(FunctionDefinition(when, body));
    return Success(());
  }

  method ResolveAllAxioms(ers: ExprResolverState) returns (r: Result<seq<Axiom>, string>)
    requires ers.Valid()
    modifies ers.functionMap.Values`ExplainedBy
    ensures forall f: Function :: old(allocated(f) && f.WellFormed()) ==> f.WellFormed()
    ensures r.Success? ==> forall axiom <- ers.b3.axioms :: axiom.WellFormed(ers.b3, {})
    ensures r.Success? ==> forall axiom <- r.value :: axiom.WellFormed()
  {
    var b3 := ers.b3;
    var resolvedAxioms: seq<Axiom> := [];
    for n := 0 to |b3.axioms|
      invariant forall f: Function :: old(allocated(f) && f.WellFormed()) ==> f.WellFormed()
      // the axioms seen so far are well-formed
      invariant forall axiom <- b3.axioms[..n] :: axiom.WellFormed(b3, {})
      invariant forall axiom <- resolvedAxioms :: axiom.WellFormed()
   {
      var axiom := b3.axioms[n];
      var resolvedExplains := [];
      for i := 0 to |axiom.explains|
        invariant forall f: Function :: old(allocated(f) && f.WellFormed()) ==> f.WellFormed()
        invariant forall func <- resolvedExplains :: func in ers.functionMap.Values
      {
        var name := axiom.explains[i];
        if name !in ers.functionMap {
          return Failure("undeclared function: " + name);
        }
        var func := ers.functionMap[name];
        assert func in ers.functionMap.Values;
        resolvedExplains := resolvedExplains + [func];
      }
      assert (map[] as map<string, Variable>).Keys == {};
      var expr :- ResolveExpr(axiom.expr, ers, map[]);

      var resolvedAxiom := new Axiom(resolvedExplains, expr);
      for i := 0 to |resolvedExplains|
        invariant forall f: Function :: old(allocated(f) && f.WellFormed()) ==> f.WellFormed()
      {
        var func := resolvedExplains[i];
        func.ExplainedBy := func.ExplainedBy + [resolvedAxiom];
      }
      resolvedAxioms := resolvedAxioms + [resolvedAxiom];
    }

    return Success(resolvedAxioms);
  }

  method ResolveAllProcedures(ers: ExprResolverState) returns (r: Result<map<string, Procedure>, string>, procedures: seq<Procedure>)
    requires ers.Valid()
    ensures r.Success? ==>
      // raw procedures had distinct names and were well-formed
      && (forall i, j :: 0 <= i < j < |ers.b3.procedures| ==> ers.b3.procedures[i].name != ers.b3.procedures[j].name)
      && (forall proc <- ers.b3.procedures :: proc.WellFormed(ers.b3, ers.generatedTypes))
    ensures r.Success? ==> var procMap: map<string, Procedure> := r.value;
      && procMap.Keys == (set proc <- ers.b3.procedures :: proc.name)
      && NameAlignment(procMap)
      && LinearForm(procMap, procedures)
    ensures r.Success? ==>
      // the resolved procedures returned have distinct names, are freshly allocated, and are well-formed
      && NamedDecl.Distinct(procedures)
      && fresh(procedures)
      && (forall proc <- procedures :: proc.WellFormed())
  {
    var b3 := ers.b3;
    var procMap: map<string, Procedure> := map[];
    procedures := [];
    for n := 0 to |b3.procedures|
      // properties of the raw procedures seen so far
      invariant forall i, j :: 0 <= i < j < n ==> b3.procedures[i].name != b3.procedures[j].name
      invariant procMap.Keys == set proc <- b3.procedures[..n] :: proc.name
      invariant forall proc <- b3.procedures[..n] :: proc.SignatureWellFormed(b3, ers.generatedTypes) && procMap[proc.name].SignatureCorrespondence(proc)
      // properties of procMap
      invariant NameAlignment(procMap)
      invariant LinearForm(procMap, procedures)
      // properties of procedures
      invariant NamedDecl.Distinct(procedures)
      invariant |procedures| == n && fresh(procedures)
      invariant forall proc <- procedures :: proc.WellFormed()
/*
      invariant forall proc <- b3.procedures[..n] ::
        && proc.SignatureWellFormed(b3)
        && procMap[proc.name].SignatureWellFormed(proc)
        && procMap[proc.name].WellFormedHeader()
*/
   {
      var proc := b3.procedures[n];
      var name := proc.name;
      if name in procMap.Keys {
        return Failure("duplicate procedure name: " + name), procedures;
      }
      var rProc :- ResolveProcedureSignature(proc, ers);
      NewNamePreservesLinearFormAndIsUnique(name, rProc, procMap, procedures);
      procMap := procMap[name := rProc];
      procedures := procedures + [rProc];
    }

    var prs := ProcResolverState(ers, Some(procMap));
    for n := 0 to |b3.procedures|
      invariant forall proc <- b3.procedures :: proc.SignatureWellFormed(b3, ers.generatedTypes) && procMap[proc.name].SignatureCorrespondence(proc)
      invariant forall proc <- b3.procedures[..n] :: proc.WellFormed(b3, ers.generatedTypes)
      invariant forall proc <- procedures :: proc.WellFormed()
    {
      var proc := b3.procedures[n];
      var rProc := procMap[proc.name];
      assert rProc in procedures by {
        LinearFormL2R(proc.name, procMap, procedures);
      }
      var _ :- ResolveProcedureBody(proc, rProc, prs);
    }

    return Success(procMap), procedures;
  }

  method ResolveProcedureSignature(proc: Raw.Procedure, ers: ExprResolverState) returns (r: Result<Procedure, string>)
    requires ers.Valid()
    ensures r.Success? ==> proc.SignatureWellFormed(ers.b3, ers.generatedTypes)
    ensures r.Success? ==> fresh(r.value) && r.value.SignatureCorrespondence(proc) && r.value.WellFormed()
  {
    var paramMap: map<string, Variable> := map[];
    var formals: seq<PParameter> := [];
    for n := 0 to |proc.parameters|
      invariant forall p <- proc.parameters[..n] :: Raw.LegalVariableName(p.name) && (ers.b3.IsType(p.typ) || p.typ in ers.generatedTypes)
      invariant forall i, j :: 0 <= i < j < n ==> proc.parameters[i].name != proc.parameters[j].name
      invariant paramMap.Keys ==
        (set p <- proc.parameters[..n] :: p.name) +
        (set p <- proc.parameters[..n] | p.mode == Raw.InOut :: Raw.OldName(p.name))
      invariant |formals| == n && fresh(formals)
      invariant forall i :: 0 <= i < n ==> formals[i] == paramMap[proc.parameters[i].name]
      invariant forall i :: 0 <= i < n ==> formals[i].name == proc.parameters[i].name
      invariant forall i :: 0 <= i < n ==> formals[i].mode == proc.parameters[i].mode
      invariant forall i :: 0 <= i < n ==> (formals[i].oldInOut.Some? <==> proc.parameters[i].mode == Raw.InOut)
    {
      var p := proc.parameters[n];
      if !Raw.LegalVariableName(p.name) {
        return Failure("illegal parameter name: " + p.name);
      } else if p.name in paramMap {
        return Failure("duplicate parameter name: " + p.name);
      }
      var typ :- ResolveType(p.typ, ers.typeMap);

      var oldInOut;
      if p.mode == Raw.InOut {
        var oldName := Raw.OldName(p.name);
        forall pp <- proc.parameters[..n]
          ensures pp.name != oldName
        {
          assert Raw.LegalVariableName(pp.name);
          reveal Raw.LegalVariableName;
        }
        var v := new LocalVariable(oldName, false, typ);
        oldInOut := Some(v);
        paramMap := paramMap[oldName := v];
      } else {
        oldInOut := None;
      }

      var formal := new PParameter(p.name, p.mode, typ, oldInOut);
      paramMap := paramMap[p.name := formal];
      formals := formals + [formal];
    }

    var preScope := set p <- proc.parameters | p.mode.IsIncoming() :: p.name;
    var postScope := (set p <- proc.parameters :: p.name) + (set p <- proc.parameters | p.mode == Raw.InOut :: Raw.OldName(p.name));

    var preVariables := MapProject(paramMap, preScope);
    assert preVariables.Keys == preScope;
    var preLs := LocalResolverState(preVariables, map[], None, None);
    var pre :- ResolveAExprs(proc.pre, ers, preLs);

    var postVariables := MapProject(paramMap, postScope);
    assert postVariables.Keys == postScope;
    var postLs := LocalResolverState(postVariables, map[], None, None);
    var post :- ResolveAExprs(proc.post, ers, postLs);

    for n := 0 to |proc.parameters|
      modifies formals
    {
      var p := proc.parameters[n];
      var maybeAutoInv :- ResolveMaybeExpr(p.optionalAutoInv, ers, (if p.mode == Raw.In then preLs else postLs).varMap);
      formals[n].maybeAutoInv := maybeAutoInv;
    }

    var rproc := new Procedure(proc.name, formals, pre, post);
    return Success(rproc);
  }

  const ReturnLabelName: string := "return"

  method ResolveProcedureBody(proc: Raw.Procedure, rproc: Procedure, prs: ProcResolverState) returns (r: Result<(), string>)
    requires proc.SignatureWellFormed(prs.ers.b3, prs.ers.generatedTypes)
    requires rproc.SignatureCorrespondence(proc) && rproc.WellFormedHeader()
    requires prs.Valid()
    modifies rproc
    ensures r.Success? && proc.body.Some? ==>
      var postScope := proc.AllParameterNames();
      proc.body.value.WellFormed(prs.ers.b3, prs.ers.generatedTypes, postScope, {}, false)
    ensures r.Success? ==> proc.WellFormed(prs.ers.b3, prs.ers.generatedTypes) && rproc.WellFormed()
  {
    if proc.body == None {
      rproc.Body := None;
      return Success(());
    }

    var formals := rproc.Parameters;
    ghost var postScope := proc.AllParameterNames();
    forall i, j | 0 <= i < j < |formals|
      ensures Raw.OldName(formals[i].name) != Raw.OldName(formals[j].name)
    {
      var a, b := formals[i].name, formals[j].name;
      assert a != b;
      assert Raw.OldName(a)[|Raw.OldPrefix|..] == a;
    }
    var varMap: map<string, Variable> :=
      (map formal <- formals :: formal.name := formal) +
      (map formal <- formals | formal.oldInOut.Some? :: Raw.OldName(formal.name) := formal.oldInOut.value);
    assert varMap.Keys == proc.AllParameterNames();

    var returnLabel := new Label(ReturnLabelName);
    var ls := LocalResolverState(varMap, map[], None, Some(returnLabel));

    var body :- ResolveStmt(proc.body.value, prs, ls);

    rproc.Body := Some(LabeledStmt(returnLabel, body));
    return Success(());
  }
}
