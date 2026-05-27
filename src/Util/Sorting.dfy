module Sorting {
  export
    provides Sorted, SortedStrings
    provides Compare
    reveals ComparisonFunction
    provides CompareStrings

  datatype Compare = Smaller | Equal | Larger

  type ComparisonFunction<!X> = (X, X) -> Compare

  method SortedStrings(input: set<string>) returns (r: seq<string>)
    ensures |r| == |input|
    ensures forall x <- r :: x in input
  {
    r := Sorted(input, CompareStrings);
  }

  // return a sorted sequence containin the items in "input" (in quadratic time)
  method Sorted<X>(input: set<X>, cmp: ComparisonFunction) returns (r: seq<X>)
    ensures |r| == |input|
    ensures forall x <- r :: x in input
  {
    r := [];
    var ss := input;
    while ss != {}
      invariant |r| + |ss| == |input|
      invariant ss <= input
      invariant forall x <- r :: x in input
    {
      var s :| s in ss;
      ss := ss - {s};
      var p := Insert(r, s, cmp);
      r := p.output;
    }
  }

  datatype InsertResult<X> = InsertResult(output: seq<X>, ghost j: nat)

  // insert "x" into "input" at the highest position "j" where "from <= j <= |input|" and
  // every item in "input[from..j]" is strictly smaller than "x".
  function Insert<X>(input: seq<X>, x: X, cmp: ComparisonFunction, from: nat := 0): (r: InsertResult<X>)
    requires from <= |input|
    ensures from <= r.j <= |input|
    ensures r.output == input[..r.j] + [x] + input[r.j..]
    decreases |input| - from
  {
    if from == |input| then
      InsertResult(input + [x], |input|)
    else if cmp(input[from], x) == Smaller then
      Insert(input, x, cmp, from + 1)
    else
      InsertResult(input[..from] + [x] + input[from..], from)
  }

  function CompareStrings(a: string, b: string): Compare {
    CompareStringsFrom(a, b, 0)
  }

  function CompareStringsFrom(a: string, b: string, from: nat := 0): Compare
    requires from <= |a| && from <= |b|
    decreases |a| - from
  {
    if from == |a| then
      if from == |b| then Equal else Smaller
    else if from == |b| then
      Larger
    else
      var ax, bx := a[from], b[from];
      if ax < bx then
        Smaller
      else if ax > bx then
        Larger
      else
        CompareStringsFrom(a, b, from + 1)
  }
}