module DomainInstantiation {
  export
    provides Instantiate
    provides Ast, NamesAndLinearForms

  import Basics
  import Raw = RawAst
  import opened Ast
  import NamesAndLinearForms

  method Instantiate(domain: Domain, selfTypeDecl: TypeDecl, typeArguments: seq<Type>) returns (instTypes: seq<TypeDecl>, instFunctions: seq<Function>, instAxioms: seq<Axiom>, instProcedures: seq<Procedure>)
    requires Raw.LegalVariableName(selfTypeDecl.Name)
    requires |domain.params| == |typeArguments|
    requires NamedDecl.Distinct(domain.params + domain.members.types)
    ensures NamedDecl.Distinct(instTypes)
    ensures forall typ <- instTypes :: NamesAndLinearForms.HasPrefix(selfTypeDecl.Name, typ.Name)
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
  }
}