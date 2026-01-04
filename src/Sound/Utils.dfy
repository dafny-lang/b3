module Utils { 

  import opened Std.Wrappers

  function SetOfSeq<T>(s: seq<T>): set<T> {
    set x | x in s
  }

  function Index<T(==)>(ss: seq<T>, e: T): nat
    requires e in ss
    ensures Index(ss, e) < |ss|
    ensures ss[Index(ss, e)] == e
  {
    if |ss| == 1 then 
      0
    else
      if ss[0] == e then
        0
      else
        Index(ss[1..], e) + 1
  }

  function Max(s: set<nat>): (m: nat)
    requires s != {}
    ensures m in s && forall z :: z in s ==> z <= m
  {
    var x :| x in s;
    if s == {x} then
      x
    else
      var s' := s - {x};
      assert s == s' + {x};
      var y := Max(s');
      max(x, y)
  } by method {
    m :| m in s;
    var r := s - {m};
    while r != {}
      invariant r < s
      invariant m in s && forall z :: z in s - r ==> z <= m
    {
      var x :| x in r;
      assert forall z :: z in s - (r - {x}) ==> z in s - r || z == x;
      r := r - {x};
      if m < x {
        m := x;
      }
    }
    assert s - {} == s;
  }

  function Max'(s: set<nat>): (m: nat)
    ensures (s == {} || m in s) && forall z :: z in s ==> z <= m
  {
    if s == {} then 0 else Max(s)
  }

  lemma MaxLemma(s: set<nat>, i: nat, m: nat)
    requires i + m in s
    ensures i <= Max(s) - m
  {
    if s != {} {
      var x :| x in s;
    }
  }

  // function SeqTail<T>(n: nat, ss: seq<T>): seq<T> {
  //   if |ss| <= n then [] else ss[n..]
  // }

  function max(x: nat, y: nat): nat {
    if x > y then x else y
  }
  // function min(x: nat, y: nat): nat {
  //   if x < y then x else y
  // }

  // function SeqMax(ss: seq<nat>): nat 
  //   ensures forall i <- ss :: i <= SeqMax(ss)
  //   ensures forall i: nat :: i < |ss| ==> ss[i] <= SeqMax(ss)
  //   ensures ss != [] ==> SeqMax(ss) in ss
  // {
  //   if ss == [] then 
  //     0 
  //   else
  //     assert ss == [ss[0]] + (ss[1..]);
  //     max(ss[0], SeqMax(ss[1..]))
  // }

  datatype Except<+T> =
    | Ok(res: T)
    | Error
  {
    predicate IsFailure() {
      Error?
    }
    function PropagateFailure<U>(): Except<U>
      requires IsFailure()
    {
      Error
    }
    function Extract() : T 
      requires !IsFailure()
    {
      res
    }
  }
}

