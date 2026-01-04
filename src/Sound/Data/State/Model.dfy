module Model {
  import opened Utils
  export
    provides Utils,
      PreModel, PreModel.InferType, PreModel.Valid,
      PreModel.InterpLiteral,
      PreModel.InterpInt, PreModel.InterpBool, PreModel.ToInt, PreModel.ToBool,
      PreModel.Not, PreModel.Equiv, PreModel.Or, PreModel.Negate, PreModel.Plus, PreModel.Minus, PreModel.Times, PreModel.Div, PreModel.Mod, PreModel.Less, 
      PreModel.AtMost, PreModel.NoEmptyTypes, PreModel.InterpFunctionOn, PreModel.BoolIsTrueOrFalse, PreModel.TrueNotFalse
    reveals Any, Model,  Bot, PreModel,
      PreModel.True, PreModel.False, PreModel.LogicAnd, PreModel.IsBool, PreModel.IsInt, PreModel.HasType, PreModel.Implies, 
      Literal, FunctionSig, Function, Type, Int, Bool, PreModel.Eql, PreModel.Neql,
      PreModel.HaveTypes

  type Type = string
  const Int : Type := "int"
  const Bool : Type := "bool"
  datatype Literal = Literal(value: string, typ: Type)
  type FunctionSig = seq<Type>
  datatype Function = Function(name: string, sig: FunctionSig, resultType: Type)
  
  // TODO: module refinement for Any
  type Any(!new, ==)

  function {:axiom} Bot(): Any

  function {:axiom} EmbedInt(x: int): Any

  function {:axiom} EmbedBool(x: bool): Any

  /**
  lemmas about embedding and embedding back
   */

  datatype PreModel = Model(
    inferType: Any -> Type,
    interpLiteral: Literal -> Any,
    interpInt: int -> Any,
    interpBool: bool -> Any,
    toInt: Any --> int,
    toBool: Any --> bool,
    interpFunctionOn: (Function, seq<Any>) --> Any
    ) {

    ghost opaque predicate Valid() {
      && (forall typ: Type :: exists x: Any :: HasType(x, typ))
      && (forall x: Literal :: HasType(interpLiteral(x), x.typ))
      && (forall x: int :: HasType(interpInt(x), Int))
      && (forall x: bool :: HasType(interpBool(x), Bool))
      && (forall x: Any :: IsInt(x) ==> toInt.requires(x))
      && (forall x: Any :: IsBool(x) ==> toBool.requires(x))
      && (forall x: Any :: IsInt(x) ==> interpInt(toInt(x)) == x)
      && (forall x: Any :: IsBool(x) ==> interpBool(toBool(x)) == x)
      && (interpBool(true) != interpBool(false))
      && (forall func: Function, args: seq<Any> :: HaveTypes(args, func.sig) ==> interpFunctionOn.requires(func, args))
      && (forall func: Function, args: seq<Any> :: HaveTypes(args, func.sig) ==> HasType(interpFunctionOn(func, args), func.resultType))
    }
    function InferType(x: Any): Type
    {
      inferType(x)
    }
    
    predicate HasType(x: Any, typ: Type) {
      InferType(x) == typ
    }

    lemma NoEmptyTypes(typ: Type) returns (x: Any)
      requires Valid()
      ensures HasType(x, typ)
    {
      assert (forall typ: Type :: exists x: Any :: HasType(x, typ)) by {
        reveal Valid;
      }
      var x': Any :| HasType(x', typ);
      x := x';
    }

    opaque function InterpLiteral(x: Literal): Any
      requires Valid()
      ensures HasType(InterpLiteral(x), x.typ)
    {
      reveal Valid;
      interpLiteral(x)
    }

    predicate IsInt(x: Any) {
      HasType(x, Int)
    }

    predicate IsBool(x: Any) {
      HasType(x, Bool)
    }

    opaque function InterpInt(x: int): Any
      requires Valid()
      ensures HasType(InterpInt(x), Int)
    {
      reveal Valid;
      interpInt(x)
    }

    opaque function InterpBool(x: bool): Any
      requires Valid()
      ensures HasType(InterpBool(x), Bool)
    {
      reveal Valid;
      interpBool(x)
    }

    opaque function ToBool(x: Any): bool
      requires Valid()
      requires IsBool(x)
      ensures InterpBool(ToBool(x)) == x
    {
      reveal Valid;
      reveal InterpBool;
      toBool(x)
    }

    opaque function ToInt(x: Any): int
      requires Valid()
      requires IsInt(x)
      ensures InterpInt(ToInt(x)) == x
    {
      reveal Valid;
      reveal InterpInt;
      toInt(x)
    }

    function True(): Any requires Valid() { InterpBool(true) }
    function False(): Any requires Valid() { InterpBool(false) }

    lemma TrueNotFalse()
      requires Valid()
      ensures True() != False()
    {
      reveal Valid;
      reveal InterpBool;
    }

    function Eql(x: Any, y: Any): Any 
      requires Valid()
    {
      InterpBool(x == y)
    }

    function Neql(x: Any, y: Any): Any 
      requires Valid()
    {
      InterpBool(x != y)
    }

    function Not(x: Any): Any
      requires Valid()
      requires IsBool(x)
    {
      InterpBool(!ToBool(x))
    }

    function LogicAnd(x: Any, y: Any): Any
      requires Valid()
      requires IsBool(x)
      requires IsBool(y)
    {
      InterpBool(ToBool(x) && ToBool(y))
    }

    function Implies(x: Any, y: Any): Any
      requires Valid()
      requires IsBool(x)
      requires IsBool(y)
    {
      InterpBool(ToBool(x) ==> ToBool(y))
    }

    function Equiv(x: Any, y: Any): Any
      requires Valid()
      requires IsBool(x)
      requires IsBool(y)
    {
      InterpBool(ToBool(x) <==> ToBool(y))
    }

    function Or(x: Any, y: Any): Any
      requires Valid()
      requires IsBool(x)
      requires IsBool(y)
    {
      InterpBool(ToBool(x) || ToBool(y))
    }

    function Negate(x: Any): Any
      requires Valid()
      requires IsInt(x)
    {
      InterpInt(-ToInt(x))
    }

    function Plus(x: Any, y: Any): Any
      requires Valid()
      requires IsInt(x)
      requires IsInt(y)
    {
      InterpInt(ToInt(x) + ToInt(y))
    }

    function Minus(x: Any, y: Any): Any
      requires Valid()
      requires IsInt(x)
      requires IsInt(y)
    {
      InterpInt(ToInt(x) - ToInt(y))
    }

    function Times(x: Any, y: Any): Any
      requires Valid()
      requires IsInt(x)
      requires IsInt(y)
    {
      InterpInt(ToInt(x) * ToInt(y))
    }

    function Div(x: Any, y: Any): Any
      requires Valid()
      requires IsInt(x)
      requires IsInt(y)
      requires ToInt(y) != 0
    {
      InterpInt(ToInt(x) / ToInt(y))
    }

    function Mod(x: Any, y: Any): Any
      requires Valid()
      requires IsInt(x)
      requires IsInt(y)
      requires ToInt(y) != 0
    {
      InterpInt(ToInt(x) % ToInt(y))
    }

    function Less(x: Any, y: Any): Any
      requires Valid()
      requires IsInt(x)
      requires IsInt(y)
    {
      InterpBool(ToInt(x) < ToInt(y))
    }

    function AtMost(x: Any, y: Any): Any
      requires Valid()
      requires IsInt(x)
      requires IsInt(y)
    {
      InterpBool(ToInt(x) <= ToInt(y))
    }

    predicate HaveTypes(args: seq<Any>, sig: FunctionSig) {
      |args| == |sig| && forall i :: 0 <= i < |args| ==> HasType(args[i], sig[i])
    }

    opaque function InterpFunctionOn(func: Function, args: seq<Any>): Any
      requires Valid()
      requires HaveTypes(args, func.sig)
      ensures HasType(InterpFunctionOn(func, args), func.resultType)
    {
      reveal Valid;
      interpFunctionOn(func, args)
    }

    lemma BoolIsTrueOrFalse(x: Any)
      requires Valid()
      requires IsBool(x)
      ensures x == True() || x == False()
    {
      reveal Valid;
      reveal InterpBool;
      assert x == InterpBool(ToBool(x));
    }
  }
    
  
  type Model = m: PreModel | m.Valid() witness *

  // predicate

}