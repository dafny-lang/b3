module Types {
  // Types

  type TypeName = string

  const BoolTypeName := "bool"
  const IntTypeName := "int"
  const TagTypeName := "tag"
  const BuiltInTypes: set<TypeName> := {BoolTypeName, IntTypeName, TagTypeName}

  datatype Type =
    | BoolType
    | IntType
    | TagType
    | UserType(decl: TypeDecl)
  {
    function ToString(): string {
      match this
      case BoolType => BoolTypeName
      case IntType => IntTypeName
      case TagType => TagTypeName
      case UserType(decl) => decl.Name
    }
  }

  class TypeDecl {
    const Name: string
    
    constructor (name: string)
      ensures Name == name
    {
      Name := name;
    }
  }
}