// This module defines two predicates that are used during resolution:
//     * NameAlignment
//     * LinearForm
// along with some useful lemmas about these.

module NamesAndLinearForms {
  import Ast
  import Raw = RawAst

  export
    reveals NameAlignment, LinearForm, HasPrefix
    provides LinearFormValues, LinearFormL2R, LinearFormR2L, NewNamePreservesLinearForm, NewNamePreservesLinearFormAndIsUnique
    provides DistinctConcat, PrefixOf, PrefixIsUnique
    provides Ast, Raw

  ghost predicate NameAlignment(xMap: map<string, Ast.NamedDecl>) {
    forall name <- xMap :: xMap[name].Name == name
  }

  // LinearForm(xMap, xs) says that the image of xMap is the set of elements in xs.
  ghost predicate LinearForm<X>(xMap: map<string, X>, xs: seq<X>) {
    (set name <- xMap :: xMap[name]) == set x <- xs
  }

  // Like LinearForm, LinearFormValues(xMap, xs) says that the image of xMap is the set of elements in xs.
  // but LinearFormValues expresses this property in terms of the map's .Values.
  lemma LinearFormValues<X>(xMap: map<string, X>, xs: seq<X>)
    requires LinearForm(xMap, xs)
    ensures xMap.Values == set x <- xs
  {
  }

  lemma LinearFormL2R<X>(name: string, xMap: map<string, X>, xs: seq<X>)
    requires LinearForm(xMap, xs) && name in xMap
    ensures xMap[name] in xs
  {
    var lhs := set name <- xMap :: xMap[name];
    var rhs := set x <- xs;
    assert xMap[name] in lhs;
    assert xMap[name] in rhs;
  }

  lemma LinearFormR2L<X>(x: X, xMap: map<string, X>, xs: seq<X>) returns (name: string)
    requires LinearForm(xMap, xs) && x in xs
    ensures name in xMap && xMap[name] == x
  {
    var lhs := set name <- xMap :: xMap[name];
    var rhs := set x <- xs;
    assert x in rhs;
    assert x in lhs;
    name :| name in xMap && xMap[name] == x;
  }

  lemma NewNamePreservesLinearFormAndIsUnique(name: string, decl: Ast.NamedDecl, xMap: map<string, Ast.NamedDecl>, xs: seq<Ast.NamedDecl>)
    requires NameAlignment(xMap)
    requires LinearForm(xMap, xs)
    requires name !in xMap
    requires decl.Name == name
    ensures forall i :: 0 <= i < |xs| ==> xs[i].Name != name
    ensures LinearForm(xMap[name := decl], xs + [decl])
  {
    NewNameIsUnique(name, decl, xMap, xs);
    NewNamePreservesLinearForm(name, decl, xMap, xs);
  }

  lemma NewNamePreservesLinearForm<X>(name: string, decl: X, xMap: map<string, X>, xs: seq<X>)
    requires LinearForm(xMap, xs)
    requires name !in xMap
    ensures LinearForm(xMap[name := decl], xs + [decl])
  {
    var xMap', xs' := xMap[name := decl], xs + [decl];
    var n := |xs|;
    calc {
      (set xName <- xMap' :: xMap'[xName]);
      (set xName <- xMap :: xMap'[xName]) + {xMap'[name]};
      { assert name !in xMap; }
      (set xName <- xMap :: xMap[xName]) + {decl};
      { assert LinearForm(xMap, xs); }
      (set x <- xs) + {decl};
      { assert xs == xs'[..n] && xs'[n] == decl; }
      (set x <- xs'[..n]) + {xs'[n]};
      (set x <- xs');
    }
  }

  lemma NewNameIsUnique(name: string, decl: Ast.NamedDecl, xMap: map<string, Ast.NamedDecl>, xs: seq<Ast.NamedDecl>)
    requires NameAlignment(xMap)
    requires LinearForm(xMap, xs)
    requires name !in xMap
    requires decl.Name == name
    ensures forall i :: 0 <= i < |xs| ==> xs[i].Name != name
  {
    forall i | 0 <= i < |xs|
      ensures xs[i].Name != name
    {
      // From the definition of LinearForm:
      var lhs := set xName <- xMap :: xMap[xName];
      var rhs := set x <- xs;
      assert lhs == rhs; // by LinearForm(xMap, xs)

      var x := xs[i];
      assert x in xs;
      assert x in rhs;
      assert x in lhs;
      var xName :| xName in xMap && xMap[xName] == x;
      assert xMap[xName].Name == xName;
      assert xName != name; // since "xName in xMap" and "name !in xMap"
    }
  }

  lemma DistinctConcat(xMap: map<string, Ast.NamedDecl>, xs: seq<Ast.NamedDecl>, yMap: map<string, Ast.NamedDecl>, ys: seq<Ast.NamedDecl>)
    requires LinearForm(xMap, xs) && LinearForm(yMap, ys)
    requires NameAlignment(xMap) && NameAlignment(yMap)
    requires xMap.Keys !! yMap.Keys
    requires Ast.NamedDecl.Distinct(xs) && Ast.NamedDecl.Distinct(ys)
    ensures Ast.NamedDecl.Distinct(xs + ys)
  {
    var decls := xs + ys;
    forall i, j | 0 <= i < j < |decls|
      ensures decls[i].Name != decls[j].Name
    {
      var n := |xs|;
      assert decls[..n] == xs && decls[n..] == ys;
      if j < n {
        assert decls[i] in xs && decls[j] in xs;
      } else if n <= i {
        assert decls[i] in ys && decls[j] in ys;
      } else {
        assert decls[i].Name in xMap by {
          var name := LinearFormR2L(decls[i], xMap, xs);
          assert xMap[name].Name == name; // by NameAlignment
        }
        assert decls[j].Name in yMap by {
          var name := LinearFormR2L(decls[j], yMap, ys);
          assert yMap[name].Name == name; // by NameAlignment
        }
      }
    }
  }

  predicate HasPrefix(prefix: string, name: string) {
    && Raw.LegalVariableName(prefix)
    && prefix + ".." <= name
  }

  function PrefixOf(name: string): string
    requires Raw.HasDoubleDot(name)
  {
    var j := FirstDoubleDot(name, 0);
    name[..j]
  }

  function FirstDoubleDot(name: string, i: nat): (j: nat)
    requires i <= |name| && Raw.HasDoubleDot(name[i..])
    ensures i <= j < |name| - 1 && name[j] == '.' == name[j + 1]
    ensures forall k :: i <= k < j ==> name[k] != '.' || name[k + 1] != '.'
    decreases |name| - i
  {
    Raw.AboutDoubleDot(name[i..]);
    ghost var m :| 0 <= m < |name[i..]| - 1 && name[i..][m] == '.' == name[i..][m + 1];
    assert name[i + m] == '.' == name[i + m + 1];
    if name[i] == '.' == name[i + 1] then
      i
    else
      assert m != 0;
      assert 0 <= m - 1 < |name[i + 1..]| - 1 && name[i + 1..][m - 1] == '.' == name[i + 1..][m];
      Raw.AboutDoubleDot(name[i + 1..]);
      FirstDoubleDot(name, i + 1)
  }

  lemma PrefixIsUnique(prefix: string, name: string)
    requires HasPrefix(prefix, name) && Raw.LegalVariableName(prefix)
    ensures (Raw.ProveHasDoubleDot(name, |prefix|); PrefixOf(name) == prefix)
  {
    var m := |prefix|;
    assert name[..m] == prefix;
    assert name[m] == '.' == name[m + 1];

    Raw.ProveHasDoubleDot(name, m);
    var j := FirstDoubleDot(name, 0);
    assert PrefixOf(name) == name[..j];

    // From postconditions of FirstDoubleDot:
    assert 0 <= j < |name| - 1 && name[j] == '.' == name[j + 1];
    assert forall k :: 0 <= k < j ==> name[k] != '.' || name[k + 1] != '.'; // j is the first double dot

    if
    case m < j =>
      // No, j cannot be bigger than m, because there is a double dot at m and j is the first double dot
      assert false;
    case j == m - 1 =>
      // No, because "prefix" is a legal variable name, so it cannot end with a dot
      reveal Raw.LegalVariableName;
      assert false;
    case j < m - 1 =>
      // No, because "prefix" has no double dot
      reveal Raw.LegalVariableName;
      Raw.ProveHasDoubleDot(prefix, j);
      assert false;
    case j == m =>
      // This is the only remain case
  }
}