module DomainResolver {
  import opened Std.Wrappers
  import opened Basics
  import Raw = RawAst
  import opened Ast
  import opened NamesAndLinearForms
  import opened TypeResolver
  import DomainInstantiation

  // "domain" is the resolved Domain, as declared in the program.
  // "selfTypeDecl" is the TypeDecl corresponding to the LHS of the domain-instantiation declaration.
  // "typeArguments" are the resolved types corresponding to the type arguments of the RHS of the domain-instantiation declaration.
  datatype ResolvedInstantiation = ResolvedInstantiation(domain: Domain, selfTypeDecl: TypeDecl, typeArguments: seq<Type>) {
    predicate WellFormed() {
      && (forall func <- domain.members.functions :: func.SignatureWellFormed())
      && (forall axiom <- domain.members.axioms :: axiom.WellFormed())
      && Raw.LegalVariableName(selfTypeDecl.Name)
      && |domain.params| == |typeArguments|
      && NamedDecl.Distinct(domain.params + domain.members.types)
    }
  }

  method ResolveDomainInstantiations(b3: Raw.Program, domainMap: map<string, Domain>, typeMap: map<string, TypeDecl>) returns (r: Result<seq<ResolvedInstantiation>, string>)
    requires forall i, j :: 0 <= i < j < |b3.types| ==> b3.types[i].name != b3.types[j].name
    requires forall domainName <- domainMap :: var domain := domainMap[domainName];
      && domain.WellFormed()
      && (forall func <- domain.members.functions :: func.SignatureWellFormed())
    requires forall typ <- b3.types :: typ.name in typeMap && Raw.LegalVariableName(typ.name)
    requires NameAlignment(typeMap)
    ensures r.Success? ==> var resolvedInstantiations := r.value;
      && (forall ri <- resolvedInstantiations :: ri.WellFormed())
      && (forall i, j :: 0 <= i < j < |resolvedInstantiations| ==> resolvedInstantiations[i].selfTypeDecl.Name != resolvedInstantiations[j].selfTypeDecl.Name)
  {
    var resolvedInstantiations := [];
    for n := 0 to |b3.types|
      invariant forall ri: ResolvedInstantiation <- resolvedInstantiations ::
        && ri.WellFormed()
        && exists i :: 0 <= i < n && ri.selfTypeDecl.Name == b3.types[i].name
      invariant forall i, j :: 0 <= i < j < |resolvedInstantiations| ==> resolvedInstantiations[i].selfTypeDecl.Name != resolvedInstantiations[j].selfTypeDecl.Name
    {
      match b3.types[n].domainInstantiation
      case None =>
      case Some(instantiation) =>
        var selfTypeDecl := typeMap[b3.types[n].name];
        var domainName := instantiation.name;
        if domainName !in domainMap {
          return Failure("unknown domain: " + domainName);
        }
        var domain := domainMap[domainName];
        if |domain.params| != |instantiation.typeArguments| {
          var got := Int2String(|instantiation.typeArguments|);
          var expected := Int2String(|domain.params|);
          return Failure("domain instantiation has wrong number of type arguments: " + domainName + " (got " + got + ", expected " + expected + ")");
        }
        var resolvedTypeArguments := [];
        for j := 0 to |instantiation.typeArguments|
          invariant |resolvedTypeArguments| == j
        {
          var resolvedType :- ResolveType(instantiation.typeArguments[j], typeMap);
          resolvedTypeArguments := resolvedTypeArguments + [resolvedType];
        }
        assert Raw.LegalVariableName(selfTypeDecl.Name);
        assert NamedDecl.Distinct(domain.params + domain.members.types) by {
          var internalTypes := [domain.self] + domain.params + domain.members.types;
          assert NamedDecl.Distinct(internalTypes); // by domain.WellFormed()
          var exportedTypes := domain.params + domain.members.types;
          assert NamedDecl.Distinct(exportedTypes) by {
            assert forall i :: 0 <= i < |exportedTypes| ==> exportedTypes[i] == internalTypes[i + 1];
          }
        }
        forall i | 0 <= i < |resolvedInstantiations|
          ensures resolvedInstantiations[i].selfTypeDecl.Name != selfTypeDecl.Name
        {
          assert resolvedInstantiations[i] in resolvedInstantiations;
          var j :| 0 <= j < n && resolvedInstantiations[i].selfTypeDecl.Name == b3.types[j].name;
          assert selfTypeDecl.Name == b3.types[n].name;
          assert b3.types[j].name != b3.types[n].name;
        }
        var ri := ResolvedInstantiation(domain, selfTypeDecl, resolvedTypeArguments);
        assert ri.WellFormed() by {
          assume {:axiom} forall axiom <- domain.members.axioms :: axiom.WellFormed(); // TODO
        }
        resolvedInstantiations := resolvedInstantiations + [ri];
    }

    return Success(resolvedInstantiations);
  }

  method InstantiateDomains(resolvedInstantiations: seq<ResolvedInstantiation>) returns (instTypes: seq<TypeDecl>, instFunctions: seq<Function>, instAxioms: seq<Axiom>, instProcedures: seq<Procedure>)
    requires forall ri <- resolvedInstantiations :: ri.WellFormed()
    requires forall i, j :: 0 <= i < j < |resolvedInstantiations| ==> resolvedInstantiations[i].selfTypeDecl.Name != resolvedInstantiations[j].selfTypeDecl.Name
    ensures NamedDecl.Distinct(instTypes)
    ensures forall typ <- instTypes :: Raw.HasDoubleDot(typ.Name)
    ensures forall axiom <- instAxioms :: axiom.WellFormed()
  {
    instTypes, instFunctions, instAxioms, instProcedures := [], [], [], [];
    for i := 0 to |resolvedInstantiations|
      invariant forall typ <- instTypes :: Raw.HasDoubleDot(typ.Name)
      invariant forall typ <- instTypes :: exists j :: 0 <= j < i && HasPrefix(resolvedInstantiations[j].selfTypeDecl.Name, typ.Name)
      invariant NamedDecl.Distinct(instTypes)
      invariant forall axiom <- instAxioms :: axiom.WellFormed()
    {
      var instantiation := resolvedInstantiations[i];
      assert instantiation.WellFormed();
      assume {:axiom} forall func <- instantiation.domain.members.functions :: func.WellFormed(); // TODO
      var tt: seq<TypeDecl>, ff, aa, pp := DomainInstantiation.Instantiate(instantiation.domain, instantiation.selfTypeDecl, instantiation.typeArguments);

      // Prove the invariants about the new "tt"
      forall typ <- tt
        ensures Raw.HasDoubleDot(typ.Name)
      {
        Raw.ProveHasDoubleDot(typ.Name, |instantiation.selfTypeDecl.Name|);
      }
      assert NamedDecl.Distinct(tt);
      forall typ0 <- instTypes, typ1 <- tt
        ensures typ0.Name != typ1.Name
      {
        var j :| 0 <= j < i && HasPrefix(resolvedInstantiations[j].selfTypeDecl.Name, typ0.Name); // from loop invariant
        assert HasPrefix(resolvedInstantiations[i].selfTypeDecl.Name, typ1.Name); // from call to DomainInstantiation.Instantiate

        assert PrefixOf(typ0.Name) == resolvedInstantiations[j].selfTypeDecl.Name by {
          assert resolvedInstantiations[j].WellFormed();
          PrefixIsUnique(resolvedInstantiations[j].selfTypeDecl.Name, typ0.Name);
        }
        assert PrefixOf(typ1.Name) == resolvedInstantiations[i].selfTypeDecl.Name by {
          assert resolvedInstantiations[i].WellFormed();
          PrefixIsUnique(resolvedInstantiations[i].selfTypeDecl.Name, typ1.Name);
        }

        assert resolvedInstantiations[j].selfTypeDecl.Name != resolvedInstantiations[i].selfTypeDecl.Name;
      }

      instTypes, instFunctions, instAxioms, instProcedures := instTypes + tt, instFunctions + ff, instAxioms + aa, instProcedures + pp;
    }
  }
}