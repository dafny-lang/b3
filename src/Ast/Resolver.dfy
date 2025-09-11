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

  method Resolve(b3: Raw.Program) returns (r: Result<Ast.Program, string>)
    ensures r.Success? ==> b3.WellFormed() && r.value.WellFormed()
  {
    var typeMap :- ResolveAllTypes(b3);
    var taggerMap :- ResolveAllTaggers(b3, typeMap);
    var functionMap :- ResolveAllFunctions(b3, typeMap, taggerMap);
    CombineMaps(taggerMap, functionMap);
    functionMap := taggerMap + functionMap;
    var ers := ExprResolverState(b3, typeMap, functionMap);
    var axioms :- ResolveAllAxioms(ers);
    var procMap :- ResolveAllProcedures(ers);

    var types := SeqMap(b3.types, typeName requires typeName in typeMap => typeMap[typeName]);
    var tagAndFunctionNames :=
      SeqMap(b3.taggers, (tagger: Raw.Tagger) => tagger.name) +
      SeqMap(b3.functions, (func: Raw.Function) => func.name);
    var functions := SeqMap(tagAndFunctionNames, (name: string) requires name in functionMap => functionMap[name]);
    var procedures := SeqMap(b3.procedures, (proc: Raw.Procedure) requires proc.name in procMap => procMap[proc.name]);
    var r3 := Program(types, functions, axioms, procedures);

    r3 :- FunctionDesugaring.Desugar(r3);

    return Success(r3);
  }

  ghost predicate NameAlignment(functionMap: map<string, Function>) {
    && (forall functionName <- functionMap :: functionMap[functionName].Name == functionName)
    && (var functions: set<Function> := functionMap.Values;
         forall func0 <- functions, func1 <- functions :: func0.Name == func1.Name ==> func0 == func1)
  }

  lemma CombineMaps(a: map<string, Function>, b: map<string, Function>)
    requires a.Keys !! b.Keys
    requires NameAlignment(a) && NameAlignment(b)
    ensures (a + b).Values == a.Values + b.Values
    ensures NameAlignment(a + b)
  {
  }

  method ResolveAllTypes(b3: Raw.Program) returns (r: Result<map<string, TypeDecl>, string>)
    ensures r.Success? ==> var typeMap := r.value;
      && typeMap.Keys == (set typename <- b3.types)
      && MapIsInjective(typeMap)
      && (forall typename <- typeMap :: typeMap[typename].Name == typename)
      && (forall typename <- b3.types :: typename !in BuiltInTypes)
      && (forall i, j :: 0 <= i < j < |b3.types| ==> b3.types[i] != b3.types[j])
  {
    var typeMap: map<string, TypeDecl> := map[];
    for n := 0 to |b3.types|
      // typeMap maps user-defined types seen so far to distinct type-declaration objects
      invariant typeMap.Keys == set typename <- b3.types[..n]
      invariant MapIsInjective(typeMap)
      // typeMap organizes type-declaration objects correctly according to their names
      invariant forall typename <- typeMap :: typeMap[typename].Name == typename
      // no user-defined type seen so far uses the name of a built-in type
      invariant forall typename <- b3.types[..n] :: typename !in BuiltInTypes
      // the user-defined types seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.types[i] != b3.types[j]
    {
      var name := b3.types[n];
      if name in BuiltInTypes {
        return Result<map<string, TypeDecl>, string>.Failure("user-defined type is not allowed to have the name of a built-in type: " + name);
      } else if name in typeMap.Keys {
        return Failure("duplicate type name: " + name);
      }
      var decl := new TypeDecl(name);
      typeMap := typeMap[name := decl];
    }
    return Success(typeMap);
  }

  method ResolveAllTaggers(b3: Raw.Program, typeMap: map<string, TypeDecl>) returns (r: Result<map<string, Function>, string>)
    requires forall typename :: b3.IsType(typename) <==> typename in BuiltInTypes || typename in typeMap
    ensures r.Success? ==>
      && (forall i, j :: 0 <= i < j < |b3.taggers| ==> b3.taggers[i].name != b3.taggers[j].name)
      && (forall tagger <- b3.taggers :: tagger.WellFormed(b3))
    ensures r.Success? ==> var taggerMap: map<string, Function> := r.value;
      && taggerMap.Keys == (set tagger <- b3.taggers :: tagger.name)
      && NameAlignment(taggerMap)
    ensures r.Success? ==> var taggers: set<Function> := r.value.Values;
      && fresh(taggers)
      && (forall tagger <- taggers :: tagger.WellFormedAsTagger())
  {
    var taggerMap: map<string, Function> := map[];
    for n := 0 to |b3.taggers|
      // taggerMap maps the user-defined taggers seen so far to distinct and fresh tagger-declaration objects
      invariant taggerMap.Keys == set tagger <- b3.taggers[..n] :: tagger.name
      invariant MapIsInjective(taggerMap)
      invariant forall name <- taggerMap :: fresh(taggerMap[name])
      // taggerMap organizes tagger-declaration objects correctly according to their names
      invariant forall taggerName <- taggerMap :: taggerMap[taggerName].Name == taggerName
      // taggers seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.taggers[i].name != b3.taggers[j].name
      // the taggers seen so far are well-formed
      invariant forall tagger <- b3.taggers[..n] :: tagger.WellFormed(b3) && taggerMap[tagger.name].WellFormedAsTagger()
    {
      var tagger := b3.taggers[n];
      var name := tagger.name;
      if name in taggerMap.Keys {
        return Failure("duplicate tagger name: " + name);
      }
      var typ :- ResolveType(tagger.typ, typeMap);

      var parameter := new FParameter("subject", false, typ);
      var rTagger := new Function(name, [parameter], Types.TagType, None);
      taggerMap := taggerMap[name := rTagger];
    }
    return Success(taggerMap);
  }

  method ResolveAllFunctions(b3: Raw.Program, typeMap: map<string, TypeDecl>, taggerMap: map<string, Function>) returns (r: Result<map<string, Function>, string>)
    requires forall typename :: b3.IsType(typename) <==> typename in BuiltInTypes || typename in typeMap
    requires forall taggerName <- taggerMap :: taggerMap[taggerName].Name == taggerName && taggerMap[taggerName].WellFormedAsTagger()
    ensures r.Success? ==>
      && (forall i, j :: 0 <= i < j < |b3.functions| ==> b3.functions[i].name != b3.functions[j].name)
      && (forall func <- b3.functions :: func.WellFormed(b3))
    ensures r.Success? ==> var functions: set<Function> := r.value.Values;
      && fresh(functions)
      && (forall func <- functions :: func.WellFormed())
    ensures r.Success? ==> var functionMap := r.value;
      && taggerMap.Keys !! functionMap.Keys
      && NameAlignment(functionMap)
      && (forall functionName <- functionMap :: exists func <- b3.functions :: func.name == functionName)
      && (forall rawFunction <- b3.functions ::
            && rawFunction.name in functionMap
            && var func := functionMap[rawFunction.name];
            && |rawFunction.parameters| == |func.Parameters|
         )
  {
    var functionMap: map<string, Function> := map[];
    for n := 0 to |b3.functions|
      // functionMap maps the user-defined functions seen so far to distinct and fresh function-declaration objects
      invariant functionMap.Keys == set func <- b3.functions[..n] :: func.name
      invariant MapIsInjective(functionMap)
      invariant forall name <- functionMap :: fresh(functionMap[name])
      // user-defined functions don't have the same names as taggers
      invariant taggerMap.Keys !! functionMap.Keys
      // functionMap organizes function-declaration objects correctly according to their names
      invariant forall functionName <- functionMap :: functionMap[functionName].Name == functionName
      // functions seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.functions[i].name != b3.functions[j].name
      // the functions seen so far are well-formed
      invariant forall func <- b3.functions[..n] :: func.SignatureWellFormed(b3) && functionMap[func.name].SignatureWellFormed(func)
    {
      var func := b3.functions[n];
      var name := func.name;
      if name in taggerMap.Keys {
        return Failure("function and tagger have the same name: " + name);
      }
      if name in functionMap.Keys {
        return Failure("duplicate function name: " + name);
      }
      var rfunc :- ResolveFunctionSignature(func, b3, typeMap, taggerMap);
      functionMap := functionMap[name := rfunc];
    }

    var ers := ExprResolverState(b3, typeMap, functionMap);
    for n := 0 to |b3.functions|
      invariant forall func <- b3.functions :: func.SignatureWellFormed(b3) && functionMap[func.name].SignatureWellFormed(func)
      invariant forall func <- b3.functions[..n] :: func.WellFormed(b3)
      invariant forall func <- b3.functions[..n] :: functionMap[func.name].WellFormed()
    {
      var func := b3.functions[n];
      var _ :- ResolveFunction(func, functionMap[func.name], ers);
    }

    return Success(functionMap);
  }

  method ResolveFunctionSignature(func: Raw.Function, b3: Raw.Program, typeMap: map<string, TypeDecl>, taggerMap: map<string, Function>) returns (r: Result<Function, string>)
    requires forall typename :: b3.IsType(typename) <==> typename in BuiltInTypes || typename in typeMap
    requires forall taggerName <- taggerMap :: taggerMap[taggerName].Name == taggerName && taggerMap[taggerName].WellFormedAsTagger()
    ensures r.Success? ==> func.SignatureWellFormed(b3)
    ensures r.Success? ==> fresh(r.value) && r.value.SignatureWellFormed(func)
  {
    var paramMap: map<string, Variable> := map[];
    var formals: seq<FParameter> := [];
    for n := 0 to |func.parameters|
      invariant forall p <- func.parameters[..n] :: Raw.LegalVariableName(p.name) && b3.IsType(p.typ)
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

  method ResolveFunction(func: Raw.Function, rfunc: Function, ers: ExprResolverState) returns (r: Result<(), string>)
    requires func.SignatureWellFormed(ers.b3) && rfunc.SignatureWellFormed(func) && ers.Valid()
    modifies rfunc
    ensures r.Success? ==> func.WellFormed(ers.b3) && rfunc.WellFormed()
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
    requires forall functionName <- ers.functionMap :: ers.functionMap[functionName].WellFormed()
    modifies ers.functionMap.Values
    ensures forall functionName <- ers.functionMap :: ers.functionMap[functionName].WellFormed()
    ensures r.Success? ==> forall axiom <- ers.b3.axioms :: axiom.WellFormed(ers.b3, {})
    ensures r.Success? ==> forall axiom <- r.value :: axiom.WellFormed()
  {
    var b3 := ers.b3;
    var resolvedAxioms: seq<Axiom> := [];
    for n := 0 to |b3.axioms|
      invariant forall functionName <- ers.functionMap :: ers.functionMap[functionName].WellFormed()
      // the axioms seen so far are well-formed
      invariant forall axiom <- b3.axioms[..n] :: axiom.WellFormed(b3, {})
      invariant forall axiom <- resolvedAxioms :: axiom.WellFormed()
   {
      var axiom := b3.axioms[n];
      var resolvedExplains := [];
      for i := 0 to |axiom.explains|
        invariant forall functionName <- ers.functionMap :: ers.functionMap[functionName].WellFormed()
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
        invariant forall functionName <- ers.functionMap :: ers.functionMap[functionName].WellFormed()
      {
        var func := resolvedExplains[i];
        func.ExplainedBy := func.ExplainedBy + [resolvedAxiom];
      }
      resolvedAxioms := resolvedAxioms + [resolvedAxiom];
    }

    return Success(resolvedAxioms);
  }

  method ResolveAllProcedures(ers: ExprResolverState) returns (r: Result<map<string, Procedure>, string>)
    requires ers.Valid()
    ensures r.Success? ==>
      && (forall i, j :: 0 <= i < j < |ers.b3.procedures| ==> ers.b3.procedures[i].name != ers.b3.procedures[j].name)
      && (forall proc <- ers.b3.procedures :: proc.WellFormed(ers.b3))
    ensures r.Success? ==> var procMap: map<string, Procedure> := r.value;
      procMap.Keys == (set proc <- ers.b3.procedures :: proc.name)
    ensures r.Success? ==> var procedures: set<Procedure> := r.value.Values;
      && (forall proc0 <- procedures, proc1 <- procedures :: proc0.Name == proc1.Name ==> proc0 == proc1)
      && (forall proc <- procedures :: proc.WellFormed())
  {
    var b3 := ers.b3;
    var procMap: map<string, Procedure> := map[];
    for n := 0 to |b3.procedures|
      // procMap maps the user-defined procedures seen so far to distinct and fresh procedure-declaration objects
      invariant procMap.Keys == set proc <- b3.procedures[..n] :: proc.name
      invariant MapIsInjective(procMap)
      invariant forall name <- procMap :: fresh(procMap[name])
      // procMap organizes procedure-declaration objects correctly according to their names
      invariant forall procname <- procMap :: procMap[procname].Name == procname
      // user-defined types seen so far have distinct names
      invariant forall i, j :: 0 <= i < j < n ==> b3.procedures[i].name != b3.procedures[j].name
      // the procedures seen so far are well-formed
      invariant forall proc <- b3.procedures[..n] ::
        && proc.SignatureWellFormed(b3)
        && procMap[proc.name].SignatureWellFormed(proc)
        && procMap[proc.name].WellFormedHeader()
   {
      var proc := b3.procedures[n];
      var name := proc.name;
      if name in procMap.Keys {
        return Failure("duplicate procedure name: " + name);
      }
      var rproc :- ResolveProcedureSignature(proc, ers);
      procMap := procMap[name := rproc];
    }

    var prs := ProcResolverState(ers, Some(procMap));
    for n := 0 to |b3.procedures|
      invariant forall proc <- b3.procedures[..n] :: proc.WellFormed(b3) && procMap[proc.name].WellFormed()
    {
      var proc := b3.procedures[n];
      var _ :- ResolveProcedureBody(proc, procMap[proc.name], prs);
    }

    return Success(procMap);
  }

  method ResolveProcedureSignature(proc: Raw.Procedure, ers: ExprResolverState) returns (r: Result<Procedure, string>)
    requires ers.Valid()
    ensures r.Success? ==> proc.SignatureWellFormed(ers.b3)
    ensures r.Success? ==> fresh(r.value) && r.value.SignatureWellFormed(proc) && r.value.WellFormedHeader()
  {
    var paramMap: map<string, Variable> := map[];
    var formals: seq<Parameter> := [];
    for n := 0 to |proc.parameters|
      invariant forall p <- proc.parameters[..n] :: Raw.LegalVariableName(p.name) && ers.b3.IsType(p.typ)
      invariant forall i, j :: 0 <= i < j < n ==> proc.parameters[i].name != proc.parameters[j].name
      invariant paramMap.Keys ==
        (set p <- proc.parameters[..n] :: p.name) +
        (set p <- proc.parameters[..n] | p.mode == Raw.InOut :: Raw.OldName(p.name))
      invariant |formals| == n
      invariant forall i :: 0 <= i < n ==> formals[i] == paramMap[proc.parameters[i].name]
      invariant forall i :: 0 <= i < n ==> formals[i].name == proc.parameters[i].name
      invariant forall i :: 0 <= i < n ==> formals[i].mode == proc.parameters[i].mode
      invariant forall i :: 0 <= i < n ==> (formals[i].oldInOut.Some? <==> proc.parameters[i].mode == Raw.InOut)
    {
      var p := proc.parameters[n];
      if !Raw.LegalVariableName(p.name) {
        return Failure("illegal parameter name: " + p.name);
      }
      if p.name in paramMap {
        return Failure("duplicate parameter name: " + p.name);
      }
      var typ :- ResolveType(p.typ, ers.typeMap);

      var oldInOut;
      if p.mode == Raw.InOut {
        var v := new LocalVariable(Raw.OldName(p.name), false, typ);
        oldInOut := Some(v);
        paramMap := paramMap[Raw.OldName(p.name) := v];
      } else {
        oldInOut := None;
      }

      var formal := new Parameter(p.name, p.mode, typ, oldInOut);
      paramMap := paramMap[p.name := formal];
      formals := formals + [formal];
    }

    var preScope := set p <- proc.parameters | p.mode.IsIncoming() :: p.name;
    var postScope := (set p <- proc.parameters :: p.name) + (set p <- proc.parameters | p.mode == Raw.InOut :: Raw.OldName(p.name));

    var preVariables := MapProject(paramMap, preScope);
    assert preVariables.Keys == preScope;
    var pre :- ResolveAExprs(proc.pre, ers, LocalResolverState(preVariables, map[], None, None));

    var postVariables := MapProject(paramMap, postScope);
    assert postVariables.Keys == postScope;
    var ls := LocalResolverState(postVariables, map[], None, None);
    var post :- ResolveAExprs(proc.post, ers, ls);

    var rproc := new Procedure(proc.name, formals, pre, post);
    return Success(rproc);
  }

  method ResolveType(typename: string, typeMap: map<string, TypeDecl>) returns (r: Result<Type, string>)
    ensures r.Success? ==> typename in BuiltInTypes || typename in typeMap
  {
    if typename == BoolTypeName {
      return Success(BoolType);
    } else if typename == IntTypeName {
      return Success(IntType);
    } else if typename == TagTypeName {
      return Success(TagType);
    }

    if typename !in typeMap {
      return Failure("unknown type: " + typename);
    }
    return Success(UserType(typeMap[typename]));
  }

  datatype ProcResolverState = ProcResolverState(ers: ExprResolverState, maybeProcMap: Option<map<string, Procedure>>)
  {
    ghost predicate Valid() {
      && ers.Valid()
      && match maybeProcMap {
        case None => true
        case Some(procMap) =>
          && (forall procname <- procMap :: exists proc <- ers.b3.procedures :: proc.name == procname)
          && (forall rawProc <- ers.b3.procedures ::
                && rawProc.name in procMap
                && var proc := procMap[rawProc.name];
                && |rawProc.parameters| == |proc.Parameters|
                && (forall i :: 0 <= i < |rawProc.parameters| ==> rawProc.parameters[i].mode == proc.Parameters[i].mode)
            )
      }
    }
  }

  datatype ExprResolverState = ExprResolverState(b3: Raw.Program, typeMap: map<string, TypeDecl>, functionMap: map<string, Function>)
  {
    ghost predicate Valid() {
      && (forall typename :: b3.IsType(typename) <==> typename in BuiltInTypes || typename in typeMap)
      && (forall functionName <- functionMap ::
            || (exists func <- b3.taggers :: func.name == functionName)
            || (exists func <- b3.functions :: func.name == functionName)
         )
      && (forall rawFunction <- b3.functions ::
            && rawFunction.name in functionMap
            && var func := functionMap[rawFunction.name];
            && |rawFunction.parameters| == |func.Parameters|
         )
    }
  }

  datatype LocalResolverState = LocalResolverState(
    varMap: map<string, Variable>,
    labelMap: map<string, Label>,
    loopLabel: Option<Label>,
    returnLabel: Option<Label>)
  {
    function AddVariable(name: string, v: Variable): LocalResolverState
      ensures AddVariable(name, v).varMap.Keys == varMap.Keys + {name}
    {
      this.(varMap := varMap[name := v])
    }

    function FindLabel(name: string): Result<Label, string> {
      if name in labelMap then
        Success(labelMap[name])
      else
        Failure("undeclared exit label: " + name)
    }

    function LabelSet(): set<string>
      ensures labelMap == map[] ==> LabelSet() == {}
    {
      labelMap.Keys
    }

    function AddLabel(name: string, lbl: Label): LocalResolverState
      ensures AddLabel(name, lbl).labelMap.Keys == labelMap.Keys + {name}
    {
      this.(labelMap := labelMap[name := lbl])
    }

    method GenerateLoopLabel() returns (lbl: Label, ls: LocalResolverState)
      ensures ls.varMap.Keys == varMap.Keys
      ensures ls.LabelSet() == LabelSet()
      ensures ls.loopLabel.Some?
    {
      lbl := new Label("loop");
      ls := this.(loopLabel := Some(lbl));
    }
  }

  const ReturnLabelName: string := "return"

  method ResolveProcedureBody(proc: Raw.Procedure, rproc: Procedure, prs: ProcResolverState) returns (r: Result<(), string>)
    requires proc.SignatureWellFormed(prs.ers.b3)
    requires rproc.SignatureWellFormed(proc) && rproc.WellFormedHeader()
    requires prs.Valid()
    modifies rproc
    ensures r.Success? && proc.body.Some? ==>
      var postScope := proc.AllParameterNames();
      proc.body.value.WellFormed(prs.ers.b3, postScope, {}, false)
    ensures r.Success? ==> proc.WellFormed(prs.ers.b3) && rproc.WellFormed()
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

  method ResolveAExprs(aexprs: seq<Raw.AExpr>, ers: ExprResolverState, ls: LocalResolverState) returns (r: Result<seq<AExpr>, string>)
    requires ers.Valid()
    ensures r.Success? ==> forall ae <- aexprs :: ae.WellFormed(ers.b3, ls.varMap.Keys)
    ensures r.Success? ==> forall ae <- r.value :: ae.WellFormed()
  {
    var result := [];
    for n := 0 to |aexprs|
      invariant forall ae <- aexprs[..n] :: ae.WellFormed(ers.b3, ls.varMap.Keys)
      invariant forall ae: AExpr <- result :: ae.WellFormed()
    {
      var ae :- ResolveAExpr(aexprs[n], ers, ls);
      result := result + [ae];
    }
    return Success(result);
  }

  method ResolveAExpr(aexpr: Raw.AExpr, ers: ExprResolverState, ls: LocalResolverState) returns (r: Result<AExpr, string>)
    requires ers.Valid()
    ensures r.Success? ==> aexpr.WellFormed(ers.b3, ls.varMap.Keys)
    ensures r.Success? ==> r.value.WellFormed()
  {
    match aexpr
    case AExpr(e) =>
      var expr :- ResolveExpr(e, ers, ls.varMap);
      return Success(AExpr(expr));
    case AAssertion(s) =>
      var prs := ProcResolverState(ers, None);
      var stmt :- ResolveStmt(s, prs, ls.(labelMap := map[], loopLabel := None));
      return Success(AAssertion(stmt));
  }

  method ResolveStmt(stmt: Raw.Stmt, prs: ProcResolverState, ls: LocalResolverState) returns (result: Result<Stmt, string>)
    requires prs.Valid()
    ensures result.Success? ==> stmt.WellFormed(prs.ers.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
    ensures result.Success? ==> result.value.WellFormed()
  {
    var r: Stmt;
    match stmt {
      case VarDecl(variable, init, body) =>
        if !Raw.LegalVariableName(variable.name) {
          return Failure("illegal variable name: " + variable.name);
        }
        var i;
        if init == None {
          i := None;
        } else {
          var e :- ResolveExpr(init.value, prs.ers, ls.varMap);
          i := Some(e);
        }
        var typ;
        match variable.optionalType {
          case None =>
            if i == None {
              return Failure("variable declaration must give a type or an initializing expression (or both)");
            }
            typ := i.value.ExprType();
          case Some(typeName) =>
            typ :- ResolveType(typeName, prs.ers.typeMap);
        }
        var v := new LocalVariable(variable.name, variable.isMutable, typ);
        var ls' := ls.AddVariable(variable.name, v);
        assert ls'.varMap.Keys == ls.varMap.Keys + {v.name};
        var b :- ResolveStmt(body, prs, ls');
        r := VarDecl(v, i, b);

      case Assign(lhs, rhs) =>
        if lhs !in ls.varMap {
          return Failure("undeclared variable: " + lhs);
        }
        var left := ls.varMap[lhs];
        var right :- ResolveExpr(rhs, prs.ers, ls.varMap);
        r := Assign(left, right);

      case Block(stmts) =>
        var ss := [];
        for n := 0 to |stmts|
          invariant forall stmt <- stmts[..n] :: stmt.WellFormed(prs.ers.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
          invariant forall stmt: Stmt <- ss :: stmt.WellFormed()
        {
          var s :- ResolveStmt(stmts[n], prs, ls);
          ss := ss + [s];
        }
        r := Block(ss);

      case Call(_, _) =>
        r :- ResolveCallStmt(stmt, prs, ls);

      case Check(cond) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        r := Check(c);

      case Assume(cond) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        r := Assume(c);

      case Assert(cond) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        r := Assert(c);

      case AForall(name, typ, body) =>
        if !Raw.LegalVariableName(name) {
          return Failure("illegal variable name: " + name);
        }
        var t :- ResolveType(typ, prs.ers.typeMap);
        var v := new LocalVariable(name, false, t);
        var b :- ResolveStmt(body, prs, ls.AddVariable(name, v));
        r := AForall(v, b);

      case Choose(branches) =>
        if |branches| == 0 {
          return Failure("a choose statement must have at least 1 branch");
        }
        var rbranches := [];
        for n := 0 to |branches|
          invariant forall branch <- branches[..n] ::
            branch.WellFormed(prs.ers.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
          invariant forall branch: Stmt <- rbranches :: branch.WellFormed()
        {
          var rbranch :- ResolveStmt(branches[n], prs, ls);
          rbranches := rbranches + [rbranch];
        }
        r := Choose(rbranches);

      case If(cond, thn, els) =>
        var c :- ResolveExpr(cond, prs.ers, ls.varMap);
        var th :- ResolveStmt(thn, prs, ls);
        var el :- ResolveStmt(els, prs, ls);
        var branch0 := PrependAssumption(c, th);
        var branch1 := PrependAssumption(Expr.CreateNegation(c), el);
        r := Choose([branch0, branch1]);

      case IfCase(cases) =>
        if |cases| == 0 {
          return Failure("an if-case statement must have at least 1 case");
        }
        var branches := [];
        for n := 0 to |cases|
          invariant forall cs <- cases[..n] ::
            && cs.cond.WellFormed(prs.ers.b3, ls.varMap.Keys)
            && cs.body.WellFormed(prs.ers.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
          invariant forall branch: Stmt <- branches :: branch.WellFormed()
        {
          var cond :- ResolveExpr(cases[n].cond, prs.ers, ls.varMap);
          var body :- ResolveStmt(cases[n].body, prs, ls);
          branches := branches + [PrependAssumption(cond, body)];
        }
        r := Choose(branches);

      case Loop(invariants, body) =>
        var invs :- ResolveAExprs(invariants, prs.ers, ls);
        var loopLabel, ls' := ls.GenerateLoopLabel();
        var b :- ResolveStmt(body, prs, ls');
        r := LabeledStmt(loopLabel, Loop(invs, b));
        assert stmt.WellFormed(prs.ers.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?) by {
          assert forall ae <- invariants :: ae.WellFormed(prs.ers.b3, ls.varMap.Keys);
          assert ls.varMap.Keys == ls'.varMap.Keys;
          assert ls.LabelSet() == ls'.LabelSet();
          assert ls'.loopLabel.Some?;
          assert body.WellFormed(prs.ers.b3, ls'.varMap.Keys, ls'.LabelSet(), ls'.loopLabel.Some?);
        }

      case LabeledStmt(lbl, body) =>
        if lbl in ls.labelMap {
          return Failure("duplicate label name: " + lbl);
        }
        var l := new Label(lbl);
        var b :- ResolveStmt(body, prs, ls.AddLabel(lbl, l));
        r := LabeledStmt(l, b);

      case Exit(maybeLabel) =>
        match maybeLabel {
          case None =>
            if ls.loopLabel == None {
              return Failure("an 'exit' statement outside a loop requires a label");
            }
            r := Exit(ls.loopLabel.value);
          case Some(name) =>
            var lbl :- ls.FindLabel(name);
            r := Exit(lbl);
        }

      case Return =>
        if ls.returnLabel == None {
          return Failure("a 'return' statement cannot be used here");
        }
        r := Exit(ls.returnLabel.value);

      case Probe(expr) =>
        var e :- ResolveExpr(expr, prs.ers, ls.varMap);
        r := Probe(e);
    }
    return Success(r);
  }

  method ResolveCallStmt(stmt: Raw.Stmt, prs: ProcResolverState, ls: LocalResolverState) returns (result: Result<Stmt, string>)
    requires stmt.Call? && prs.Valid()
    ensures result.Success? ==> stmt.WellFormed(prs.ers.b3, ls.varMap.Keys, ls.LabelSet(), ls.loopLabel.Some?)
    ensures result.Success? ==> result.value.WellFormed()
  {
    var Call(name, args) := stmt;

    var proc;
    match prs.maybeProcMap {
      case None =>
        return Failure("procedure calls are not allowed in this context: " + name);
      case Some(procMap) =>
        if name !in procMap {
          return Failure("call to undeclared procedure: " + name);
        }
        proc := procMap[name];
    }

    var rawProc :| rawProc in prs.ers.b3.procedures && rawProc.name == name;
    assert |rawProc.parameters| == |proc.Parameters|;

    if |args| != |proc.Parameters| {
      return Failure("wrong number of arguments in call to procedure " + name);
    }
    assert |args| == |rawProc.parameters|;

    var aa: seq<CallArgument> := [];
    for n := 0 to |args|
      invariant forall i :: 0 <= i < n ==> args[i].mode == rawProc.parameters[i].mode
      invariant forall i :: 0 <= i < n ==> args[i].arg.WellFormed(prs.ers.b3, ls.varMap.Keys)
      invariant |aa| == n
      invariant forall i :: 0 <= i < n ==> aa[i].CorrespondingMode() == proc.Parameters[i].mode && aa[i].WellFormed()
    {
      if args[n].mode != proc.Parameters[n].mode {
        return Failure("mismatched parameter mode in call to procedure " + name);
      }
      var e :- ResolveExpr(args[n].arg, prs.ers, ls.varMap);
      var ca;
      if args[n].mode == Raw.In {
        ca := InArgument(e);
      } else if !e.IdExpr? {
        return Failure(Printer.ParameterMode(args[n].mode) + "argument must be a variable");
      } else {
        ca := OutgoingArgument(args[n].mode == Raw.InOut, e.v);
      }
      aa := aa + [ca];
    }

    return Success(Call(proc, aa));
  }

  function PrependAssumption(expr: Expr, stmt: Stmt): (r: Stmt)
    requires expr.WellFormed() && stmt.WellFormed()
    ensures r.WellFormed()
  {
    if stmt.Block? then
      Block([Assume(expr)] + stmt.stmts)
    else
      Block([Assume(expr), stmt])
  }

  method ResolveExpr(expr: Raw.Expr, ers: ExprResolverState, varMap: map<string, Variable>) returns (result: Result<Expr, string>)
    ensures result.Success? ==> expr.WellFormed(ers.b3, varMap.Keys)
    ensures result.Success? ==> result.value.WellFormed()
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
          return Failure("custom literal is not allowed for a built-in type: " + Ast.CustomLiteralToString(s, typeName));
        }
        r := CustomLiteral(s, typ);
      case IdExpr(name) =>
        if name !in varMap {
          return Failure("undeclared variable: " + name);
        }
        r := IdExpr(varMap[name]);
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
        for n := 0 to |bindings|
          invariant varMap'.Keys == varMap.Keys + set binding <- bindings[..n] :: binding.name
        {
          var binding := bindings[n];
          if !Raw.LegalVariableName(binding.name) {
            return Failure("illegal variable name: " + binding.name);
          }
          var typ :- ResolveType(binding.typ, ers.typeMap);
          var quantifiedVariable := new LocalVariable(binding.name, false, typ);
          boundVars := boundVars + [quantifiedVariable];
          varMap' := varMap'[binding.name := quantifiedVariable];
        }
        assert varMap'.Keys == varMap.Keys + set binding <- bindings :: binding.name;
        var b :- ResolveExpr(body, ers, varMap');
        var trs :- ResolvePatterns(patterns, ers, varMap');
        r := QuantifierExpr(univ, boundVars, trs, b);
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
}
