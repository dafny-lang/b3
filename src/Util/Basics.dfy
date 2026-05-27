module Basics {
  import Std.Collections.Seq

  datatype List<X> = Nil | Cons(head: X, tail: List<X>)
  {
    function Append(moreTail: List<X>): List<X> {
      if this.Nil? then moreTail else
      Cons(head, tail.Append(moreTail))
    }
    const DoubleCons? := Cons? && tail.Cons?

    lemma AboutDoubleCons()
      ensures DoubleCons? <==> 2 <= Length()
    {
    }

    function Length(): nat {
      if this == Nil then 0 else 1 + tail.Length()
    }

    predicate Forall(p: X --> bool)
      requires forall x: X :: x < this ==> p.requires(x)
    {
      match this
      case Nil => true
      case Cons(x, tail) => p(x) && tail.Forall(p)
    }

    predicate Exists(p: X --> bool)
      requires forall x: X :: x < this ==> p.requires(x)
    {
      match this
      case Nil => false
      case Cons(x, tail) => p(x) || tail.Exists(p)
    }

    function Map<Y>(f: X -> Y): List<Y> {
      match this
      case Nil => Nil
      case Cons(x, tail) => Cons(f(x), tail.Map(f))
    }

    function MapPartial<Y>(f: X --> Y): List<Y>
      requires Forall(x => f.requires(x))
    {
      match this
      case Nil => Nil
      case Cons(x, tail) => Cons(f(x), tail.MapPartial(f))
    }

    lemma ForallToPartialPre<Y>(p: X -> bool, f: X --> Y)
      requires Forall(p)
      requires forall x :: p(x) ==> f.requires(x)
      ensures Forall(x => f.requires(x))
    {
    }

    static function FromSeq(s: seq<X>): List<X> {
      if s == [] then Nil else Cons(s[0], FromSeq(s[1..]))
    }

    function ToReverseSeq(): seq<X> {
      if Nil? then [] else tail.ToReverseSeq() + [head]
    }
    function DropAsMuchAsHeadOf(l: List<List<X>>): (r: List<X>)
      requires ListFlatten(l) == this
      requires l.Cons?
      ensures ListFlatten(l.tail) == r
    {
      if l.head.Nil? then this
      else
       this.tail.DropAsMuchAsHeadOf(Cons(l.head.tail, l.tail))
    }
  }

  function SeqMap<X, Y>(s: seq<X>, f: X --> Y): seq<Y>
    requires forall x <- s :: f.requires(x)
  {
    seq(|s|, i requires 0 <= i < |s| => f(s[i]))
  }

  function FoldLeft<X, Z>(z: Z, s: seq<X>, f: (Z, X) -> Z): Z {
    if s == [] then
      z
    else
      FoldLeft(f(z, s[0]), s[1..], f)
  }

  function FoldLeftNonempty<X>(s: seq<X>, f: (X, X) -> X): X
    requires s != []
  {
    FoldLeft(s[0], s[1..], f)
  }

  function FoldRight<X, Z>(s: seq<X>, f: (X, Z) -> Z, z: Z): Z {
    if s == [] then
      z
    else
      var last := |s| - 1;
      FoldRight(s[..last], f, f(s[last], z))
  }

  function FoldRightNonempty<X>(s: seq<X>, f: (X, X) -> X): X
    requires s != []
  {
    var last := |s| - 1;
    FoldRight(s[..last], f, s[last])
  }

  function Prune<X>(s: seq<X>, keepers: set<X>): seq<X> {
    if s == [] then
      s
    else if s[0] in keepers then
      [s[0]] + Prune(s[1..], keepers)
    else
      Prune(s[1..], keepers)
  }

  function ListFlatten<X>(l: List<List<X>>): List<X> {
    if l.Nil? then Nil else l.head.Append(ListFlatten(l.tail))
  }

  function SeqFlatten<X>(ss: seq<seq<X>>): seq<X> {
    if ss == [] then [] else ss[0] + SeqFlatten(ss[1..])
  }

  function SeqToString<T>(s: seq<T>, f: T --> string, separator: string := ""): string
    requires forall t <- s :: f.requires(t)
  {
    Seq.Join(Seq.MapPartialFunction(f, s), separator)
  }

  lemma CommonPrefixEquality<X>(prefix: seq<X>, a: seq<X>, b: seq<X>)
    ensures prefix + a == prefix + b <==> a == b
  {
    if prefix == [] {
      assert prefix + a == a;
      assert prefix + b == b;
    } else {
      var p0, prefix' := prefix[0], prefix[1..];
      calc {
        a == b;
        { CommonPrefixEquality(prefix', a, b); }
        prefix' + a == prefix' + b;
        {
          calc {
            prefix' + a == prefix' + b;
          ==>
            [p0] + (prefix' + a) == [p0] + (prefix' + b);
          == { assert prefix + a == [p0] + (prefix' + a) && prefix + b == [p0] + (prefix' + b); }
            prefix + a == prefix + b;
          }
          calc {
            prefix + a == prefix + b;
          ==>
            (prefix + a)[1..] == (prefix + b)[1..];
          == { assert (prefix + a)[1..] == prefix' + a && (prefix + b)[1..] == prefix' + b; }
            prefix' + a == prefix' + b;
          }
        }
        prefix + a == prefix + b;
      }
    }
  }

  method SetToSeq<X>(s: set<X>) returns (r: seq<X>) {
    r := [];
    var t := s;
    while t != {} {
      var x :| x in t;
      t := t - {x};
      r := r + [x];
    }
  }

  function MapProject<X, Y>(m: map<X, Y>, s: set<X>): map<X, Y> {
    map x | x in m && x in s :: m[x]
  }

  predicate MapIsInjective<X, Y(==)>(m: map<X, Y>) {
    forall x0 <- m.Keys, x1 <- m.Keys :: x0 != x1 ==> m[x0] != m[x1]
  }

  lemma SeqContentsSplit<X>(s: seq<X>)
    requires |s| != 0
    ensures s[0] in s && forall x <- s[1..] :: x in s
  {
  }

  function Int2String(x: int): string {
    if x == 0 then
      "0"
    else if x < 0 then
      "-" + Int2StringNoLeadingZero(-x)
    else
      Int2StringNoLeadingZero(x)
  }

  function Int2StringNoLeadingZero(x: nat): string {
    if x == 0 then
      ""
    else
      var prefix := Int2StringNoLeadingZero(x / 10);
      var digit := (x % 10) as char + '0';
      prefix + [digit]
  }

  function Comma(s: seq<string>, comma: string): string {
    if 2 <= |s| then
      s[0] + comma + Comma(s[1..], comma)
    else if |s| == 1 then
      s[0]
    else
      ""
  }

  lemma AboutExtendedMapValues<X, Y>(m: map<X, Y>, x: X, y: Y)
    ensures m[x := y].Values <= m.Values + {y}
  {
  }
}
