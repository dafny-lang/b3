module Block {
  import opened Utils
  import M = Model
  import opened Expr
  import opened AST
  import opened State

  datatype Point = Point(cont: seq<Stmt>, varsInScope: set<Variable>)

  newtype Continuation = seq<Point> {

    ghost predicate IsSafe(md: M.Model) {
      forall p <- this :: SeqIsSafe(p.cont, md)
    }

    predicate ValidCalls() {
      forall p <- this :: SeqValidCalls(p.cont)
    }

    ghost opaque predicate VariablesDistinct(vars: set<Variable>) {
      if this == [] then true else
        && this[0].varsInScope <= vars
        && SeqVariablesDistinct(this[0].cont, vars - this[0].varsInScope) 
        && this[0].varsInScope !! this[1..].AllVarsInScope()
        && this[1..].VariablesDistinct(vars - this[0].varsInScope)
        // this[0].varsInScope !! vars && this[1..].VariablesDistinct(vars, this[0].varsInScope + bvars)
    }


    function FunctionsCalled(): set<Function> {
      if this == [] then {} else SeqFunctionsCalled(this[0].cont) + this[1..].FunctionsCalled()
    }

    lemma FunctionsCalledSuffix(l: nat)
      requires l < |this|
      ensures this[l..].FunctionsCalled() <= FunctionsCalled()
    {
      if l != 0 {
        assert this[l..] == [this[l]] + this[l + 1..];
        // TODO: Might be a soundness bug
        FunctionsCalledSuffix(l - 1);
      }
    }

    function Update(cont: seq<Stmt>, varsInScope: set<Variable>): Continuation {
      [Point(cont, varsInScope as set<Variable>)] + this
    }

    function VarsInScope(l: nat): set<Variable> 
      requires l <= |this|
    {
      if l == 0 then {} else this[0].varsInScope + this[1..].VarsInScope(l - 1)
    }

    function AllVarsInScope(): set<Variable> {
      if this == [] then {} else this[0].varsInScope + this[1..].AllVarsInScope()
    }

    lemma VarsInScopeLeqAll(l: nat)
      requires l <= |this|
      ensures VarsInScope(l) + this[l..].AllVarsInScope() == AllVarsInScope()
    {

    }

    lemma VarsInScopeSuffix(l: nat)
      requires l <= |this|
      ensures VarsInScope(l) == this[..l].AllVarsInScope()
    {
      if l != 0 {
        calc {
          VarsInScope(l);
        ==
          this[0].varsInScope + this[1..].VarsInScope(l - 1);
        == { this[1..].VarsInScopeSuffix(l - 1);
             assert this[1..][..l - 1] == this[1..l]; }
          this[0].varsInScope + this[1..l].AllVarsInScope();
        == { assert this[..l][1..] == this[1..l]; }
          this[..l].AllVarsInScope();
        }

      }
    }

    function Size(): nat {
      if this == [] then 0 else SeqSize(this[0].cont) + 1 + this[1..].Size()
    }

    lemma UpdateSize(cont: seq<Stmt>, varsInScope: set<Variable>)
      ensures Update(cont, varsInScope).Size() == SeqSize(cont) + Size() + 1
    {

    }

    lemma SizePrefix(l: nat)
      requires l <= |this|
      ensures this[l..].Size() <= Size()
    {
      assert this[..l] + this[l..] == this;
      SizeConcat(this[..l], this[l..]);
    }

    predicate IsDefinedOn(d: set<Variable>) {
      AllVarsInScope() <= d
    }

    predicate JumpsDefined() {
      if this == [] then true else
        SeqJumpsDefinedOn(this[0].cont, |this[1..]|) && this[1..].JumpsDefined()
    }

    predicate VarsDefined(vars: set<Variable>) 
      requires ValidCalls()
      // requires IsDefinedOn(vars)
    {
      if this == [] then true else
        && SeqIsDefinedOn(this[0].cont, vars - this[0].varsInScope) 
        && this[1..].VarsDefined(vars - this[0].varsInScope)
    }

    lemma VarsDefinedTransitivity(vars1: set<Variable>, vars2: set<Variable>)
      requires ValidCalls()
      // requires IsDefinedOn(vars1)
      requires VarsDefined(vars1)
      requires vars1 <= vars2
      ensures VarsDefined(vars2)
    {
      if this != [] {
        this[1..].VarsDefinedTransitivity(vars1 - this[0].varsInScope, vars2 - this[0].varsInScope);
      }
    }

    lemma AllVarsInScopeSuffixSucc(l: nat)
      requires l < |this|
      ensures this[..l + 1].AllVarsInScope() == this[..l].AllVarsInScope() + this[l].varsInScope
      // ensures AllVarsInScope() == this[..l + 1].AllVarsInScope()
    {
      calc {
        this[..l + 1].AllVarsInScope();
        == { this[..l + 1].VarsInScopeLeqAll(l); }
        this[..l + 1][l..].AllVarsInScope() + this[..l + 1].VarsInScope(l);
        == { assert this[..l + 1][l..] == [this[l]]; }
        this[l].varsInScope + this[..l + 1].VarsInScope(l);
        == { this[..l + 1].VarsInScopeSuffix(l); }
        this[l].varsInScope + this[..l + 1][..l].AllVarsInScope();
        == { assert this[..l + 1][..l] == this[..l]; }
        this[..l].AllVarsInScope() + this[l].varsInScope;
      }
    }

    // lemma DefinedPrefix''(l: nat, vars: set<Variable>)
    //   requires l <= |this|
    //   requires ValidCalls()
    //   // requires IsDefinedOn(vars)
    //   ensures this[..l].AllVarsInScope() <= vars
    // {
    //   VarsInScopeSuffix(l);
    //   VarsInScopeLeqAll(l);
    // }

    lemma VariablesDistinctPrefix(vars: set<Variable>, l: nat)
      requires l <= |this|
      requires VariablesDistinct(vars)
      requires IsDefinedOn(vars)
      ensures this[l..].VariablesDistinct(vars - VarsInScope(l))
      ensures this[l..].AllVarsInScope() <= vars - VarsInScope(l)
    {
      if this != [] && l != 0 {
        calc {
          VariablesDistinct(vars);
          ==> { reveal VariablesDistinct; }
          && this[1..].VariablesDistinct(vars - this[0].varsInScope)
          && this[0].varsInScope <= vars;
          ==> { VariablesDistinctDisjoint(vars, 0);
                this[1..].VariablesDistinctPrefix(vars - this[0].varsInScope, l - 1); }
          && this[l..].VariablesDistinct(vars - this[0].varsInScope - this[1..].VarsInScope(l-1))
          && this[l..].AllVarsInScope() <= vars - this[0].varsInScope - this[1..].VarsInScope(l-1);
          == { assert vars - this[0].varsInScope - this[1..].VarsInScope(l-1) == 
                      vars - (this[0].varsInScope + this[1..].VarsInScope(l-1)); }
          && this[l..].VariablesDistinct(vars - VarsInScope(l))
          && this[l..].AllVarsInScope() <= vars - VarsInScope(l);
        }
      } else {
        assert vars - {} == vars;
      }
    }

    lemma VariablesDistinctDisjoint(vars: set<Variable>, l: nat)
      requires |this| > l
      requires VariablesDistinct(vars)
      ensures this[l].varsInScope !! this[l + 1..].AllVarsInScope()
      ensures SeqVariablesDistinct(this[l].cont, vars - VarsInScope(l + 1))
    {
      if l != 0 {
        calc {
          VariablesDistinct(vars);
          ==> { reveal VariablesDistinct; }
          && this[1..].VariablesDistinct(vars - this[0].varsInScope);
          ==> { this[1..].VariablesDistinctDisjoint(vars - this[0].varsInScope, l - 1); }
          && this[l].varsInScope !! this[l+1..].AllVarsInScope()
          && SeqVariablesDistinct(this[l].cont, vars - this[0].varsInScope - this[1..].VarsInScope(l));
          == { assert vars - this[0].varsInScope - this[1..].VarsInScope(l) == 
                      vars - (this[0].varsInScope + this[1..].VarsInScope(l)); }
          && this[l].varsInScope !! this[l+1..].AllVarsInScope()
          && SeqVariablesDistinct(this[l].cont, vars - VarsInScope(l + 1));
        }
      } else {
        reveal VariablesDistinct;
        assert VarsInScope(1) == this[0].varsInScope;
      }
    }

    lemma DefinedPrefix'(l: nat, vars: set<Variable>)
      requires l < |this|
      requires ValidCalls()
      requires JumpsDefined()
      // requires VariablesDistinct(bvars)
      // requires IsDefinedOn(vars)
      requires VarsDefined(vars)
      ensures SeqJumpsDefinedOn(this[l].cont, |this[l + 1..]|) 
      // ensures this[..l + 1].AllVarsInScope() <= vars
      ensures SeqIsDefinedOn(this[l].cont, vars - this[..l + 1].AllVarsInScope())
      // ensures SeqIsDefinedOn(this[l].cont, 1000) /*SOUNDNESS BUG:*/
    {
      // DefinedPrefix''(l + 1, vars);
      if this != [] {
        if l != 0 {
          assert this[1..][l - 1] == this[l];
          assert this[1..][l - 1..] == this[l..];
          assert this[1..][..l] == this[1..l + 1];
          this[1..].DefinedPrefix'(l - 1, vars - this[0].varsInScope);
          assert SeqIsDefinedOn(this[l].cont, vars - this[0].varsInScope - this[1..l + 1].AllVarsInScope());
          assert SeqIsDefinedOn(this[l].cont, vars - this[..l + 1].AllVarsInScope());
        }
      }
    }

    lemma DefinedPrefix(l: nat, vars: set<Variable>)
      requires l <= |this|
      requires ValidCalls()
      requires JumpsDefined()
      // requires IsDefinedOn(vars)
      requires VarsDefined(vars)
      ensures this[l..].JumpsDefined()
      // ensures this[..l].AllVarsInScope() <= vars
      // ensures this[l..].IsDefinedOn(vars - this[..l].AllVarsInScope())
      ensures this[l..].VarsDefined(vars - this[..l].AllVarsInScope())
      decreases |this| - l
    {
      if l != 0 {
        if |this| != l {
          assert this[l + 1..] == this[l..][1..];
          assert this[1..][..l - 1] == this[1..l];
          assert this[1..][..l] == this[1..l + 1];
          assert this[l..][0] == this[l];
          DefinedPrefix(l + 1, vars);
          DefinedPrefix'(l, vars);
          // assert this[..l+1].AllVarsInScope() <= vars;
          assert this[..l+1].AllVarsInScope() == this[..l].AllVarsInScope() + this[l].varsInScope by {
            AllVarsInScopeSuffixSucc(l);
          }
          // calc {
          //   this[l..].IsDefinedOn(vars - this[..l].AllVarsInScope());
          //   { VarsInScopeLeqAll(l + 1); }
          //   SeqIsDefinedOn(this[l].cont, vars - this[..l].AllVarsInScope()) && 
          //     this[l+1..].IsDefinedOn(vars - this[..l].AllVarsInScope() - this[l].varsInScope);
          //   true;
          // }
          var m := vars - this[..l].AllVarsInScope();
          calc {
            this[l..].VarsDefined(m);
            { assert m - this[l].varsInScope == vars - this[..l + 1].AllVarsInScope(); }
            SeqIsDefinedOn(this[l].cont, vars - this[..l + 1].AllVarsInScope()) && 
            this[l + 1..].VarsDefined(vars - this[..l + 1].AllVarsInScope());
            SeqIsDefinedOn(this[l].cont, vars - this[..l + 1].AllVarsInScope());
            true;
          }
        } else {
          VarsInScopeLeqAll(|this|);
          VarsInScopeSuffix(|this|);
        }
      } else {
        assert vars - this[..0].AllVarsInScope() == vars;
      }
    }
  }

    lemma SizeConcat(cont1: Continuation, cont2: Continuation)
      ensures (cont1 + cont2).Size() == cont1.Size() + cont2.Size()
    {
      if cont1 == [] {
        assert cont1 + cont2 == cont2;
      } else {
        assert (cont1 + cont2)[0] == cont1[0];
        assert (cont1 + cont2)[1..] == cont1[1..] + cont2;
        SizeConcat(cont1[1..], cont2);
      }
    }

}