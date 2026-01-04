module AssignmentTarget {
  import opened Utils
  import opened AST
  import opened State
  import M = Model
  import Omni

//   export
//     provides Utils, AST, M, Omni, State, Process, Correct
//     reveals PairToSet
  
  newtype VarsJumps = map<nat, set<Variable>> {

    ghost function Get(n: nat): iset<Variable> {
      iset i: Variable | In(i, n)
    }

    ghost predicate In(i: Variable, n: nat) 
    {
      n in Keys && i in this[n]
    }      

    function Merge(m1: VarsJumps): VarsJumps {
      map i: nat | i in Keys + m1.Keys :: 
        if i in Keys then
          if i in m1.Keys then
            this[i] + m1[i]
          else this[i]
        else m1[i]
    }

    function Remove0(): VarsJumps {
      var s0 := if 0 in Keys then this[0] else {};
      map i: nat | i in Keys - {0} :: this[i] + s0
    }

    opaque function SeqMerge(m: VarsJumps): VarsJumps {
      var s0 := if 0 in Keys then this[0] else {};
      map i: nat | i in (Keys - {0}) + m.Keys :: 
        if i in Keys then
          if i in m.Keys then
            this[i] + s0 + m[i]
          else this[i]
        else m[i] + s0
    }

    lemma SeqMergeKeys(m: VarsJumps)
      ensures SeqMerge(m).Keys == Keys - {0} + m.Keys
    {
      reveal SeqMerge(m);
    }

    lemma SeqMergeGet1(m: VarsJumps, i: Variable, k: nat)
      requires i in Get(0)
      requires k in m.Keys
      ensures i in SeqMerge(m).Get(k)
    {
      reveal SeqMerge(m);
    }

    lemma SeqMergeGet1'(m: VarsJumps, i: Variable, k: nat)
      requires i in Get(k)
      requires k in Keys
      requires k != 0
      ensures i in SeqMerge(m).Get(k)
    {
      reveal SeqMerge(m);
    }

    lemma SeqMergeGet2(m: VarsJumps, i: Variable, k: nat)
      requires i in m.Get(k)
      requires k in m.Keys
      ensures i in SeqMerge(m).Get(k)
    {
      reveal SeqMerge(m);
      var k' :| k' <= k && k' in m.Keys && i in m[k'];
    }

    function SubstractSet(vars: set<Variable>, s: set<Variable>): set<Variable> 
      // ensures forall i: Variable :: i + n in s ==> i in SubstractSet(n, s)
    {
      s - vars
      // set i: Variable {:trigger i + n in s} | i <= Max'(s) - n && i + n in s 
    }

    opaque function Substract(vars: set<Variable>): VarsJumps 
    {
      var m: VarsJumps := map i: nat {: trigger} | 
        && i <= Max'(Keys) + 1
        && i + 1 in Keys :: SubstractSet(vars, this[i + 1]);
      if 0 in m.Keys && 0 in Keys then 
        m[0 := m[0] + SubstractSet(vars, this[0])]
      else if 0 in Keys then 
        m[0 := SubstractSet(vars, this[0])]
      else m
    }

    lemma SubstractPlusOne(vars: set<Variable>, i: nat)
      requires i + 1 in Keys
      ensures i in Substract(vars).Keys
    {
      reveal Substract(vars);
    }

    lemma SubstractZero(vars: set<Variable>)
      requires 0 in Keys
      ensures 0 in Substract(vars).Keys
    {
      reveal Substract(vars);
    }

    lemma SubstractGetZero(vars: set<Variable>, i: Variable)
      requires i in Get(0)
      requires i !in vars
      requires 0 in Keys
      ensures i in Substract(vars).Get(0)
    {
      SubstractZero(vars);
      reveal Substract(vars);
    }

    lemma SubstractGet(vars: set<Variable>, i: Variable, k: nat)
      requires i in Get(k)
      requires k > 0
      requires i !in vars
      ensures i in Substract(vars).Get(k - 1) 
    {
      reveal Substract(vars);
    }

    lemma SubstracOfPlusOne(vars: set<Variable>, i: nat)
      requires i + 1 in Keys
      requires i in Substract(vars).Keys
      ensures Substract(vars)[i] >= SubstractSet(vars, this[i + 1])
    {
      reveal Substract(vars);
    }

    ghost function ToEqs(st: State, posts: Omni.Continuation): Omni.Continuation 
    {
      seq(|posts|, (k : nat) requires k < |posts| => 
        if k !in Keys then iset{} else
        iset st' |
          && st' in posts[k]
          && st'.Keys <= st.Keys
          && forall i: Variable :: i in st'.Keys && !(i in Get(k)) ==> st[i] == st'[i]
      )
    }

    ghost function ToEqsAll(st: State): iset<State>
    {
        iset st': State |
          && st'.Keys <= st.Keys
          && forall i: Variable :: i in st'.Keys && !(i in Get(0)) ==> st[i] == st'[i]
    }

    lemma GetLemma(n: nat)
      requires n in Keys
      requires n != 0
      ensures Get(n) <= Remove0().Get(n)
    {
      if 0 in Keys {
        forall i: Variable | i in Get(n) ensures i in Remove0().Get(n) {
          var k :| k <= n && k in Keys && i in this[k];
          if k != 0 {
            assert k in Remove0().Keys;
            assert this[k] <= Remove0()[k];
          } else {
            assert n in Remove0().Keys;
          }
        }
      } else {
        forall i: Variable | i in Get(n) ensures i in Remove0().Get(n) {
          var k :| k <= n && k in Keys && i in this[k];
          assert Remove0().Keys == Keys;
          assert k in Remove0().Keys;
        }
      }
    }
  }
  
  function Process'(stmt: Stmt): VarsJumps 
    requires stmt.ValidCalls()
    ensures forall v <- Process'(stmt).Values, s <- v :: s in stmt.FVars()
    decreases stmt
  {
    match stmt
    case Seq(ss) => SeqProcess'(ss)
    case Choice(s0, s1) => 
      var vs0 := Process'(s0);
      var vs1 := Process'(s1);
      vs0.Merge(vs1)
    case NewScope(n, s) => 
      var vs := Process'(s);
      reveal vs.Substract(n);
      vs.Substract(n)
    case Escape(n) => map[n := {}]
    /**
      Loop
        (x++) + (y++; exit 1)
    We need to add all m[0] vars to other m[i] because 
    loop modify 0 vars in first few operations and then
    exit modify other vars
    */
    case Loop(inv, body) => Process'(body).Remove0()
    case Assign(x, _) => map[0 := {x}]
    case Call(proc, args) => 
      args.OutArgsDepthLemma();
      map[0 := args.OutArgs()]
    case _ => map[0 := {}]
  }

  function SeqProcess'(ss: seq<Stmt>): VarsJumps 
    requires SeqValidCalls(ss)
    ensures forall v <- SeqProcess'(ss).Values, s <- v :: s in SeqFVars(ss)
    decreases ss
  {
    if ss == [] then map[0 := {}] else
      var v0 := Process'(ss[0]);
      if 0 in v0.Keys then
        reveal v0.SeqMerge(SeqProcess'(ss[1..]));
        v0.SeqMerge(SeqProcess'(ss[1..]))
      else v0
  }

  lemma Process'Correct(stmt: Stmt, st: State, m: VarsJumps, posts: Omni.Continuation, md: M.Model) 
    requires stmt.ValidCalls()
    requires Process'(stmt) == m
    ensures forall v <- m.Values, s <- v :: s in stmt.FVars()
    requires Omni.Sem(stmt, st, posts, md)
    ensures Omni.Sem(stmt, st, m.ToEqs(st, posts), md)
  {
    match stmt 
    case Choice(s0, s1) =>
      var m0 := Process'(s0);
      var m1 := Process'(s1);
      Omni.SemCons(s0, st, m0.ToEqs(st, posts), m0.Merge(m1).ToEqs(st, posts), md) by {
        Process'Correct(s0, st, m0, posts, md);
      }
      Omni.SemCons(s1, st, m1.ToEqs(st, posts), m0.Merge(m1).ToEqs(st, posts), md) by {
        Process'Correct(s1, st, m1, posts, md);
      }
    case Loop(_, body) =>
      var inv :| 
        && st in inv
        && Omni.PreservesInv(inv, body, posts, md, st);
      var m' := Process'(body);
      var inv' := inv * m'.ToEqsAll(st);
      assert st in inv';
      forall st': State | st' in inv' ensures Omni.Sem(body, st', (m'.Remove0()).ToEqs(st, posts).UpdateHead(inv'), md) {
        Omni.SemCons(body, st', m'.ToEqs(st', posts.UpdateHead(inv)), (m'.Remove0()).ToEqs(st, posts).UpdateHead(inv'), md) by {
          Process'Correct(body, st', m', posts.UpdateHead(inv), md) by {
            assert Omni.PreservesInv(inv, body, posts, md, st);
          }
        }
      }
    case NewScope(vars, s) => 
      forall vs: map<Variable, M.Any> | vs.Keys == vars ensures Omni.Sem(s, st.Update(vs), m.ToEqs(st, posts).UpdateAndAdd(vars), md) {
        var m' := Process'(s);
        Omni.SemCons(s, st.Update(vs), m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(vars)), m.ToEqs(st, posts).UpdateAndAdd(vars), md) by {
          Process'Correct(s, st.Update(vs), m', posts.UpdateAndAdd(vars), md);
          forall i: nat | i < |posts| + 1 
            ensures m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(vars))[i] <=
              m'.Substract(vars).ToEqs(st, posts).UpdateAndAdd(vars)[i]
          {
            forall st': State | st' in m'.ToEqs(st.Update(vs), posts.UpdateAndAdd(vars))[i] 
              ensures st' in m'.Substract(vars).ToEqs(st, posts).UpdateAndAdd(vars)[i] {
              assert st' in posts.UpdateAndAdd(vars)[i];
              if i == 0 {
                assert st'.Without(vars) in m'.Substract(vars).ToEqs(st, posts).head by {
                  assert forall i: Variable :: i in st'.Keys && i !in vars && !(i in m'.Get(0)) ==> st.Update(vs)[i] == st'[i];
                  if 0 in m'.Keys {
                    assert 0 in m'.Substract(vars).Keys by { m'.SubstractZero(vars); }
                    assert st'.Without(vars) in m'.Substract(vars).ToEqs(st, posts).head by {
                      forall i: Variable | i in st'.Without(vars).Keys && !(i in m'.Substract(vars).Get(0)) 
                        ensures st[i] == st'.Without(vars)[i] {
                        assert !(i in m'.Get(0) && i !in vars) by {
                          if i in m'.Get(0) && i !in vars {
                            m'.SubstractGetZero(vars, i); 
                          }
                        }
                      }
                    }
                  }
                }
              } else {
                assert st'.Without(vars) in m'.Substract(vars).ToEqs(st, posts)[i - 1] by {
                  
                  if i in m'.Keys {
                    
                    assert st'.Without(vars) in posts[i - 1] by {
                      calc {
                        st'.Without(vars) in posts[i - 1];
                        st' in posts.UpdateAndAdd(vars)[i];
                      }
                    }
                    assert (i - 1) in m'.Substract(vars).Keys by {
                      m'.SubstractPlusOne(vars, i - 1);
                    }
                    
                    forall j: Variable | j in st'.Without(vars).Keys && !(j in m'.Substract(vars).Get(i - 1)) 
                      ensures st[j] == st'.Without(vars)[j] {
                      assert !(j in m'.Get(i) && j !in vars) by {
                        if j in m'.Get(i) && j !in vars {
                          m'.SubstractGet(vars, j, i) by {
                            assert j in m'.Get(i);
                            assert i > 0;
                            assert j !in vars;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    case Seq(ss) => SeqProcess'Correct(ss, st, m, posts, md);
    case Call(proc, args) => 
      forall st': State |
        && st' in st.EqExcept(args.OutArgs())
        && st'.Keys == st.Keys
        && var callSt' := args.Eval(st') /*+ args.EvalOld(st)*/;
          (forall e <- proc.Post :: e.IsDefinedOn(callSt'.Keys) && e.HoldsOn(callSt', md))
        ensures st' in m.ToEqs(st, posts).head
      { assert st'.Keys <= st.Keys; }
    case _ =>
  }

  lemma SeqProcess'Correct(ss: seq<Stmt>, st: State, m: VarsJumps, posts: Omni.Continuation, md: M.Model) 
    requires SeqValidCalls(ss)
    requires SeqProcess'(ss) == m
    ensures forall v <- m.Values, s <- v :: s in SeqFVars(ss)
    requires Omni.SeqSem(ss, st, posts, md)
    ensures Omni.SeqSem(ss, st, m.ToEqs(st, posts), md)
  {
    if ss != [] {
      Omni.SemNest(ss[0], ss[1..], st, m.ToEqs(st, posts), md) by {
        assert Omni.Sem(ss[0], st, m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..],  m.ToEqs(st, posts), md)), md) by {
          assert Omni.Sem(ss[0], st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md)), md);
          var m' := Process'(ss[0]);
          var m'' := SeqProcess'(ss[1..]);
          Process'Correct(ss[0], st, m', posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md)), md);
          assert Omni.Sem(ss[0], st, m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md))), md);
          Omni.SemCons(ss[0], st, m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md))), 
            m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts), md)), md) by {
            assert m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md))).Leq(
              m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts), md))) by {
              if 0 in m'.Keys {
                forall i: nat | i < |posts| 
                  ensures m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md)))[i] <=
                        m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts), md))[i]
                {
                  forall st': State | st' in m'.ToEqs(st, posts.UpdateHead(Omni.SeqWP(ss[1..], posts, md)))[i] 
                    ensures st' in m.ToEqs(st, posts).UpdateHead(Omni.SeqWP(ss[1..], m.ToEqs(st, posts), md))[i]
                  {
                    if i == 0 {
                      assert forall j: Variable :: j in st'.Keys && !(j in m'.Get(0)) ==> st[j] == st'[j];
                      SeqProcess'Correct(ss[1..], st', m'', posts, md);
                      Omni.SeqSemCons(ss[1..], st', m''.ToEqs(st', posts), m'.SeqMerge(m'').ToEqs(st, posts), md) by {
                        forall i: nat | i < |posts| 
                          ensures m''.ToEqs(st', posts)[i] <= m'.SeqMerge(m'').ToEqs(st, posts)[i]
                        {
                          forall st'': State | st'' in m''.ToEqs(st', posts)[i]
                            ensures st'' in m'.SeqMerge(m'').ToEqs(st, posts)[i] {
                            if i in m''.Keys {
                              m'.SeqMergeKeys(m'');
                              forall j: Variable | j in st''.Keys && !(j in m'.SeqMerge(m'').Get(i))
                                ensures st[j] == st''[j] {
                                calc {
                                  st[j];
                                == { if j in m'.Get(0) { m'.SeqMergeGet1(m'', j, i); } }
                                  st'[j];
                                == { if j in m''.Get(i) { m'.SeqMergeGet2(m'', j, i); } }
                                  st''[j];
                                }
                              }
                            } 
                          }
                        }
                      }
                      assert Omni.SeqSem(ss[1..], st', m.ToEqs(st, posts), md);
                    } else {
                      assert st' in m'.SeqMerge(m'').ToEqs(st, posts)[i] by {
                        if i in m'.Keys {
                          m'.SeqMergeKeys(m'');
                          forall j: Variable | j in st'.Keys && !(j in m'.SeqMerge(m'').Get(i))
                            ensures st[j] == st'[j] {
                            if j in m'.Get(i) {
                              m'.SeqMergeGet1'(m'', j, i);
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  function Process(stmt: Stmt): set<Variable> 
    requires stmt.ValidCalls()
    ensures forall v <- Process(stmt) :: v in stmt.FVars()
  {
    var vs := Process'(stmt);
    if 0 in vs.Keys then vs[0] else {}
  } 

  lemma Correct'(stmt: Stmt, st: State, vars: set<Variable>, posts: Omni.Continuation, md: M.Model) 
    requires stmt.ValidCalls()
    requires forall v <- vars :: v in st.Keys
    requires Omni.Sem(stmt, st, posts, md)
    requires Process(stmt) == vars
    ensures Omni.Sem(stmt, st, posts.UpdateHead(posts.head * st.EqExcept(vars)), md)
  {
    Process'Correct(stmt, st, Process'(stmt), posts, md);
    Omni.SemCons(stmt, st, Process'(stmt).ToEqs(st, posts), posts.UpdateHead(posts.head * st.EqExcept(vars)), md);
  }

  lemma Correct(stmt: Stmt, st: State, st': State, vars: set<Variable>, posts: Omni.Continuation, post: iset<State>, md: M.Model) 
    requires stmt.ValidCalls()
    requires forall v <- vars :: v in st.Keys
    requires Omni.Sem(stmt, st, posts.UpdateHead(post), md)
    requires Process(stmt) == vars
    requires st in st'.EqExcept(vars)
    ensures Omni.Sem(stmt, st, posts.UpdateHead(post * st'.EqExcept(vars)), md)
  {
    Correct'(stmt, st, vars, posts.UpdateHead(post), md);
    assert posts.UpdateHead(post).UpdateHead(posts.UpdateHead(post).head * st.EqExcept(vars)) == posts.UpdateHead(post * st.EqExcept(vars));
    Omni.SemCons(stmt, st, posts.UpdateHead(post * st.EqExcept(vars)), posts.UpdateHead(post * st'.EqExcept(vars)), md);
  }
}