module State {
  import opened Utils
  import opened Std.Wrappers
  import M = Model

  function SomeBVal?(o: Option<M.Any>, m: M.Model): bool {
    match o
    case Some(b) => m.IsBool(b)
    case _ => false
  }

  // function SomeBValTrue?(o: Option<M.Any>): bool {
  //   match o
  //   case Some(b) => b == True
  //   case _ => false
  // }

  datatype Type = 
    | BType 
    | IType 
    | CustomType(typ: M.Type)
  {
    function ToType(): M.Type {
      match this
      case BType => M.Bool
      case IType => M.Int
      case CustomType(typ) => typ
    }
  }

  datatype Variable = Variable(name: string, typ: Type) {
    function FreshVar(vars: set<Variable>): Variable
      ensures FreshVar(vars) !in vars
      ensures FreshVar(vars).typ == typ
    {
      if vars == {} then this else
        var m := MaxLenVar(vars);
        if |name| > |m.name| then this else
        Variable(name + "$" + m.name, typ)
    }
  }

  function MaxLenVar(s: set<Variable>): (m: Variable)
    requires s != {}
    ensures m in s && forall z :: z in s ==> |z.name| <= |m.name|
  // {
  //   var x :| x in s;
  //   if s == {x} then
  //     x
  //   else
  //     var s' := s - {x};
  //     assert s == s' + {x};
  //     var y := MaxLenVar(s');
  //     if |x.name| >= |y.name| then x else y
  // } by method {
  //   m :| m in s;
  //   var r := s - {m};
  //   while r != {}
  //     invariant r < s
  //     invariant m in s && forall z :: z in s - r ==> |z.name| <= |m.name|
  //   {
  //     var x :| x in r;
  //     assert forall z :: z in s - (r - {x}) ==> z in s - r || z == x;
  //     r := r - {x};
  //     if |m.name| < |x.name| {
  //       m := x;
  //     }
  //   }
  //   assert s - {} == s;
  //   assert m in s && forall z :: z in s ==> |z.name| <= |m.name|;
  // }

  // function Singleton(val: M.Any): State
  // {
  //   [val]
  // }

  // function ToState(args: map<Variable, M.Any>): State
  // {
  //   args as State
  // }

  newtype State = map<Variable, M.Any> {

    function Update(vals: map<Variable, M.Any>): State 
    {
      ((vals + (this as map<Variable, M.Any>)) as State)
    }

    function Size(): nat {
      |this|
    }

    function UpdateAt(v: Variable, val: M.Any): State
    {
      this[v := val]
    }

    function Restrict(vars: set<Variable>): State
      ensures Restrict(vars).Keys == this.Keys * vars
    {
      map v | v in this.Keys && v in vars :: this[v]
    }

    function Without(vars: set<Variable>): State
      ensures Without(vars).Keys == this.Keys - vars
    {
      map v | v in this.Keys && v !in vars :: this[v]
    }

    // function UpdateMapShift(i: Idx, vals: map<Idx, M.Any>): State  
    //   ensures |UpdateMapShift(i, vals)| > i
    //   ensures |UpdateMapShift(i, vals)| >= |this|
    //   ensures forall v <- vals.Keys :: |UpdateMapShift(i, vals)| > v + i
    //   ensures |UpdateMapShift(i, vals)| > Max'(vals.Keys) + i
    //   ensures forall j: Idx :: j < |this| && (j < i || j - i !in vals.Keys) ==> UpdateMapShift(i, vals)[j] == this[j]
    //   ensures forall j: Idx :: j in vals.Keys ==> UpdateMapShift(i, vals)[j + i] == vals[j]
    // {
    //   var m := Max'(vals.Keys);
    //   seq(max(i + m + 1, |this|), (j: nat) requires j < max(i + m + 1, |this|) => 
    //     if j - i in vals.Keys then 
    //       vals[j - i] 
    //     else if j < |this| then
    //       this[j]
    //     else Bot()
    //   )
    // }

    // function UpdateOrAdd(i: Idx, val: M.Any): State 
    //   ensures |UpdateOrAdd(i, val)| > i
    //   ensures |UpdateOrAdd(i, val)| >= |this|
    //   ensures forall j: Idx :: j < |this| ==> j != i ==> UpdateOrAdd(i, val)[j] == this[j]
    //   ensures UpdateOrAdd(i, val)[i] == val
    // {
    //   UpdateMapShift(i, map[0 := val])
    // }

    // function MergeAt(i: Idx, vals: map<Variable, M.Any>): State 
    //   ensures |MergeAt(i, vals)| >= i + |vals|
    //   ensures |MergeAt(i, vals)| >= |this|
    //   ensures forall j: Idx :: j < |this| ==> j < i || j >= i + |vals| ==> MergeAt(i, vals)[j] == this[j]
    //   ensures forall j: Idx :: i <= j < i + |vals| ==> MergeAt(i, vals)[j] == vals[j - i]
    // {
    //   var m := map j: Idx | j < |vals| :: vals[j];
    //   ghost var m' := if m.Keys == {} then 0 else Max(m.Keys);
    //   assert m' + 1 >= |vals| by {
    //     if vals != [] {
    //       assert |vals| - 1 in m.Keys;
    //     }
    //   }
    //   UpdateMapShift(i, m)
    // }

    ghost function EqExcept(vars: set<Variable>) : iset<State>
    {
      iset st': State | 
        && st'.Keys <= Keys
        && forall v: Variable :: v in st'.Keys && v !in vars ==> st'[v] == this[v]
    }

  }

  ghost function UpdateSet(vars: set<Variable>, post: iset<State>): iset<State> 
  {
    iset st: State | st.Without(vars) in post 
  }

  ghost const   AllStates: iset<State> := iset st: State | true

  ghost function DeleteSet(vars: set<Variable>, post: iset<State>): iset<State> {
    iset st: State {:trigger} | exists st' <- post :: st == st'.Without(vars)
  }

}