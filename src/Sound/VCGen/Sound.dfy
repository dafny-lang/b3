module VCGenOmni {
  import opened Utils
  import M = Model
  import opened AST
  import opened State
  import opened Context
  import opened Expr
  import Block
  import Omni
  import AssignmentTarget

  method VCGen(s: Stmt, context_in: Context) returns (context: Context, VCs: seq<Expr>) 
    requires s.ValidCalls()
    requires s.IsDefinedOn(context_in.incarnation.Keys)
    requires s.Single()
    // requires s.IsSafe()
    ensures context_in.incarnation.Keys == context.incarnation.Keys
    ensures forall md: M.Model :: 
      s.IsSafe(md) ==>
      SeqHolds(VCs, md) ==> 
      forall st: State :: 
        context_in.IsSatisfiedOn(st, md) ==>
        Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels(md), md)
  {
    context := context_in;
    match s
    case Check(e) =>
      VCs := [context_in.MkEntailment(e)];
      forall md: M.Model, st: State | 
        && SeqHolds(VCs, md)
        && context.IsSatisfiedOn(st, md) 
        ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels(md), md) {
        context.MkEntailmentLemma(e, st, md);
      }
    case Assume(e) => 
      context := context_in.Add(e);
      VCs := [];
      forall md: M.Model, st: State | context_in.IsSatisfiedOn(st, md) 
        ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels(md), md) {
        if e.HoldsOn(context.AdjustState(st), md) {
          context_in.SubstituteIsDefinedOnLemma(e, st.Keys);
          context_in.AdjustStateSubstituteLemma(st, e, md);
        }
      }
    case Assign(v, x) =>
      ghost var vNew;
      vNew, context := context_in.AddEq(v, x);
      VCs := [];
      forall md: M.Model, st: State | context_in.IsSatisfiedOn(st, md) && s.IsSafe(md)
        ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels(md), md) {
        context_in.SubstituteIsDefinedOnLemma(x, st.Keys);
        var v' := context_in.Substitute(x).Eval(st, md);
        assert x.Eval(context_in.AdjustState(st), md) == v' by {
          context_in.AdjustStateSubstituteLemma(st, x, md);
        }
        var st' := st.UpdateAt(vNew, v'.value);
        var stTransformed := context_in.AdjustState(st)[v := v'.value];

        assert stTransformed == context.AdjustState(st') by {
          context_in.AdjustStateSubstituteLemma(st, x, md);
        }

        assert context.IsSatisfiedOn(st', md) by {
          // assert vNew !in 
          context_in.SubstituteIsDefinedOnLemma(x, context_in.incarnation.Values);
          context_in.Substitute(x).EvalFVarsLemma(st, st', md);
          EvalEqLemma(BVar(vNew), context_in.Substitute(x), st', md);

          assert forall e <- context_in.ctx :: e.HoldsOn(st, md) ==> e.HoldsOn(st', md) by 
          {
            forall e: Expr | e in context_in.ctx && e.HoldsOn(st, md) ensures e.HoldsOn(st', md) {
              e.EvalFVarsLemma(st, st', md);
            }
          }
        }
      }
    case Call(proc, args) => 
      var contextPre := context_in.mkPreContext(proc, args);
      VCs := seq(|proc.Pre|, (i: nat) requires i < |proc.Pre| => 
        SeqExprFVarsLemma(proc.Pre, proc.Pre[i]);
        contextPre.MkEntailment(proc.Pre[i]));
      var vsNew, context' := context_in.AddVarSet(args.OutArgs()) by {
        args.OutArgsDepthLemma();
      }
      var contextPost := context'.mkPostContext(proc, args/*, context_in*/);
      context := Context(contextPost.AddSeq(proc.Post).ctx, context'.incarnation);

      args.OutArgsDepthLemma();
      forall md: M.Model, st: State | 
        && SeqHolds(VCs, md)
        && context_in.IsSatisfiedOn(st, md)
        ensures Omni.SemSingle(s, context_in.AdjustState(st), context.AdjustedModels(md), md) 
      {
        var stAdj := context_in.AdjustState(st);
        var callSt := args.Eval(stAdj);
        assert args.IsDefinedOn(stAdj.Keys);
        forall e <- proc.Pre  
          ensures e.IsDefinedOn(callSt.Keys) 
          ensures e.HoldsOn(callSt, md) 
        {
          SeqExprFVarsLemma(proc.Pre, e);
          calc {
            e.HoldsOn(callSt, md);
            { context_in.mkPreContextLemma(proc, args, st); }
            e.HoldsOn(contextPre.AdjustState(st), md);
            { contextPre.MkEntailmentLemma(e, st, md); }
            contextPre.MkEntailment(e).Holds(md);
            { contextPre.MkEntailmentSeqLemma(proc.Pre, e);
              assert contextPre.MkEntailment(e) in VCs;
              assert forall e <- VCs :: e.Holds(md  ); }
            true;
          }
        }
        forall st': State | 
          && st' in stAdj.EqExcept(args.OutArgs()) 
          && st'.Keys == stAdj.Keys
          && var callSt' := args.Eval(st') /*+ args.EvalOld(stAdj)*/;
              forall e <- proc.Post :: e.IsDefinedOn(callSt'.Keys) && e.HoldsOn(callSt', md)
          ensures st' in context.AdjustedModels(md) 
          {
            forall v <- args.OutArgs() 
              ensures v in context_in.AdjustState(st).Keys {
              args.OutArgsDepthLemma();
            }
            var st'' := st + map v | v in vsNew.Keys :: st'[vsNew[v]]; //  var st'' := st.UpdateMapShift(vNew, map i: Idx | i in args.OutArgs() :: st'[i]);
            assert st' == context.AdjustState(st'');
            var callSt' := args.Eval(st') /*+ args.EvalOld(stAdj)*/;
            assert context.IsSatisfiedOn(st'', md) by {
              assert context.incarnation.Values <= st''.Keys;
              forall e <- context.ctx
                ensures e.IsDefinedOn(st''.Keys)
                ensures e.HoldsOn(st'', md) {
                if e in context_in.ctx {
                  e.EvalFVarsLemma(st, st'', md);
                } else {
                  assert e in contextPost.SeqSubstitute(proc.Post);
                  var e' := contextPost.GetSeqSubstituteLemma(proc.Post, e);
                  forall i <- contextPost.incarnation.Values
                    ensures i in st''.Keys {
                    context'.mkPostContextIncrSubsetLemma(proc, args, /*context_in,*/ i);
                  }
                  contextPost.SubstituteIsDefinedOnLemma(e', st''.Keys);
                  calc {
                    contextPost.Substitute(e').HoldsOn(st'', md);
                    { contextPost.AdjustStateSubstituteLemma(st'', e', md); }
                    e'.HoldsOn(contextPost.AdjustState(st''), md);
                    { 
                      assert contextPost.AdjustState(st'') == callSt' by {
                        assert contextPost.AdjustState(st'').Keys == callSt'.Keys == args.FVars(); /*+ args.NumInOutArgs()*/
      //                   forall i | 0 <= i < |args| + args.NumInOutArgs() 
      //                     ensures (contextPost.AdjustState(st''))[i] == callSt'[i] {
      //                     if i < |args| {
      //                       calc {
      //                         (contextPost.AdjustState(st''))[i];
      //                         == { args.IsDefinedOnIn(args[i], |context'.incarnation|);
      //                               assert context'.incarnation[args[i].v] in context'.incarnation; }
      //                         st''[context'.incarnation[args[i].v]];
      //                         ==
      //                         args.Eval(st')[i];
      //                         ==
      //                         callSt'[i];
      //                       }
      //                     } else {
      //                       calc {
      //                         (contextPost.AdjustState(st''))[i];
      //                       == { assert contextPost.incarnation[i] in contextPost.incarnation; }
      //                         st''[contextPost.incarnation[i]];
      //                       == { args.InOutArgsLemma(args.InOutArgs()[i - |args|]);
      //                             args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[i - |args|]), |context_in.incarnation|);
      //                           assert contextPost.incarnation[i] == context_in.incarnation[args.InOutArgs()[i - |args|]]; }
      //                         st''[context_in.incarnation[args.InOutArgs()[i - |args|]]];
      //                       ==
      //                         args.EvalOld(context_in.AdjustState(st))[i - |args|];
      //                       ==
      //                         callSt'[i];
      //                       }
                          // }
                        // }
                      } 
                    }
                    true;
                  }
                }
              }
            }
          }
      }
  }

  ghost function BlockWPSeq(bcont: Block.Continuation, post: iset<State>, md: M.Model) : Omni.Continuation
    ensures |BlockWPSeq(bcont, post, md)| == |bcont| + 1
    // reads *
  {
    if bcont == [] then
      [post]
    else 
      var wpSeq := BlockWPSeq(bcont[1..], post, md); // [AllStates]
      var wpNew := Omni.SeqWP(bcont[0].cont, wpSeq, md); // Omni.SeqWP(Checks, [AllStates])
      var wpSeq := wpSeq.UpdateHead(wpNew); // [Omni.SeqWP(Checks, [AllStates])]
      wpSeq.UpdateAndAdd(bcont[0].varsInScope) 
  }

  lemma BlockWPSeqIdx(bcont: Block.Continuation, l: nat, md: M.Model)
    requires l < |bcont|
    ensures BlockWPSeq(bcont, AllStates, md)[l + 1] == UpdateSet(bcont.VarsInScope(l), BlockWPSeq(bcont[l..], AllStates, md)[0])
  {
    if l != 0 {
      if |bcont| != 0 {
        var blockWP := BlockWPSeq(bcont[1..], AllStates, md);
        calc {
          BlockWPSeq(bcont, AllStates, md)[l + 1];
        ==
          blockWP.UpdateHead(Omni.SeqWP(bcont[0].cont, blockWP, md)).UpdateAndAdd(bcont[0].varsInScope)[l + 1];
        ==
          blockWP.UpdateHead(Omni.SeqWP(bcont[0].cont, blockWP, md)).Update(bcont[0].varsInScope)[l];
        == 
          UpdateSet(bcont[0].varsInScope, blockWP.UpdateHead(Omni.SeqWP(bcont[0].cont, blockWP, md))[l]);
        == { assert blockWP.UpdateHead(Omni.SeqWP(bcont[0].cont, blockWP, md))[l] == blockWP[l]; }
          UpdateSet(bcont[0].varsInScope, blockWP[l]);
        == 
          { assert blockWP[l] == UpdateSet(bcont[1..].VarsInScope(l - 1), BlockWPSeq(bcont[l..], AllStates, md)[0]) by {
            assert bcont[1..][l - 1..] == bcont[l..];
            BlockWPSeqIdx(bcont[1..], l - 1, md); 
          } }
          UpdateSet(bcont[0].varsInScope, UpdateSet(bcont[1..].VarsInScope(l - 1), BlockWPSeq(bcont[l..], AllStates, md)[0]));
        == { assert bcont.VarsInScope(l) == bcont[0].varsInScope + bcont[1..].VarsInScope(l - 1);
             assert forall st: State :: st.Without(bcont.VarsInScope(l)) == st.Without(bcont[0].varsInScope).Without(bcont[1..].VarsInScope(l - 1)); }
          UpdateSet(bcont.VarsInScope(l), BlockWPSeq(bcont[l..], AllStates, md)[0]);
          }
        }
    } else {
      calc {
        UpdateSet(bcont.VarsInScope(0), BlockWPSeq(bcont[0..], AllStates, md)[0]);
      == { assert forall st: State :: st.Without({}) == st; }
        BlockWPSeq(bcont, AllStates, md)[0];
      ==
        BlockWPSeq(bcont, AllStates, md)[1];
      }
    }
  }

  ghost predicate BlockSem(s: seq<Stmt>, bcont: Block.Continuation, st: State, post: iset<State>, md: M.Model) 
  {
    Omni.SeqSem(s, st, BlockWPSeq(bcont, post, md), md)
  }

  lemma BlockLastPost(bcont: Block.Continuation, st: State, md: M.Model)  
    requires |bcont| > 0
    requires bcont[|bcont| - 1] == Block.Point([], {}) 
    ensures st in BlockWPSeq(bcont, AllStates, md)[|bcont|]
  {
    BlockWPSeqIdx(bcont, |bcont| - 1, md);
  }

  lemma IsDefinedLoop(inv: Expr, body: Stmt, vars : set<Variable>, k: nat)
    requires body.ValidCalls()
    requires Loop(inv, body).IsDefinedOn(vars)
    requires Loop(inv, body).JumpsDefinedOn(k)
    ensures SeqIsDefinedOn([Assume(inv), body, Check(inv), Assume(BConst(false))], vars)
    ensures SeqJumpsDefinedOn([Assume(inv), body, Check(inv), Assume(BConst(false))], k)
  {
    assert [Assume(inv), body, Check(inv), Assume(BConst(false))][0] == Assume(inv);
    assert [Assume(inv), body, Check(inv), Assume(BConst(false))][1..] == [body, Check(inv), Assume(BConst(false))];
    assert [body, Check(inv), Assume(BConst(false))][0] == body;
    assert [body, Check(inv), Assume(BConst(false))][1..] == [Check(inv), Assume(BConst(false))];
    assert [Check(inv), Assume(BConst(false))][0] == Check(inv);
    assert [Check(inv), Assume(BConst(false))][1..] == [Assume(BConst(false))];
    assert [Assume(BConst(false))][0] == Assume(BConst(false));
    assert [Assume(BConst(false))][1..] == [];
  }

  // We need add allocated variables to be distinct. Otherwise, when we deallocate a variable,
  // we may delete a variable that is still in use. This is bad because we can delete an incarnation
  // that is still needed.
  method SeqVCGen(s: seq<Stmt>, context: Context, bcont: Block.Continuation) returns (VCs: seq<Expr>) 
    requires SeqValidCalls(s)
    requires bcont.ValidCalls()
    requires bcont.IsDefinedOn(context.incarnation.Keys)

    requires SeqIsDefinedOn(s, context.incarnation.Keys)
    requires SeqJumpsDefinedOn(s, |bcont|)

    requires bcont.VarsDefined(context.incarnation.Keys)
    requires bcont.JumpsDefined()

    requires SeqVariablesDistinct(s, context.incarnation.Keys)
    requires bcont.VariablesDistinct(context.incarnation.Keys)

    decreases SeqSize(s) + bcont.Size()

    ensures
      forall md: M.Model ::
        SeqIsSafe(s, md) ==>
        bcont.IsSafe(md) ==>
        SeqHolds(VCs, md) ==> 
          forall st: State:: 
            context.IsSatisfiedOn(st, md) ==> 
            BlockSem(s, bcont, context.AdjustState(st), AllStates, md)
  {
    if s == [] { 
      if bcont == [] {
        VCs := [];
        return;
      } else {
        var varsToDelete := bcont[0].varsInScope;
        var cont := bcont[0].cont;
        var context' := context.Delete(varsToDelete);
        VCs := SeqVCGen(cont, context', bcont[1..]) by {
          assert bcont.VarsInScope(1) == bcont[0].varsInScope;
          bcont.VariablesDistinctDisjoint(context.incarnation.Keys, 0);
          bcont.VariablesDistinctPrefix(context.incarnation.Keys, 1);
        }
        forall md: M.Model, st: State | 
          && SeqIsSafe([], md)
          && SeqHolds(VCs, md)
          && bcont.IsSafe(md)
          && context.IsSatisfiedOn(st, md)
          ensures BlockSem([], bcont, context.AdjustState(st), AllStates, md) 
        {
          assert bcont[1..].IsSafe(md);
          assert forall i <- context'.incarnation :: i in context.incarnation;
          assert context'.AdjustState(st) == context.AdjustState(st).Without(varsToDelete);
        }
      }
    } else {
      var stmt, cont := s[0], s[1..];
      assert s == [stmt] + cont;
      SeqSizeSplitLemma(s);
      SeqFunConcatLemmas([stmt], cont);
      if stmt.Single() {
        var VCstmt, VCcont, context';
        context', VCstmt := VCGen(stmt, context);
        VCcont := SeqVCGen(cont, context', bcont) by {
          // bcont.VariablesDistinctDisjointTransitivity(context.incarnation.Keys, SeqBVars(cont), SeqBVars(s));
          // bcont.VarsDefinedTransitivity(context.incarnation.Keys, context'.incarnation.Keys);
        }
        VCs := VCstmt + VCcont;
        forall md: M.Model, st: State | 
          && SeqIsSafe(s, md)
          && SeqHolds(VCs, md)
          && bcont.IsSafe(md)
          && context.IsSatisfiedOn(st, md)
          ensures BlockSem(s, bcont, context.AdjustState(st), AllStates, md) 
        {
          assert SeqHolds(VCstmt, md);
          assert SeqHolds(VCcont, md);
        }
      } else {
        match stmt
        case Seq(ss) =>
          VCs := SeqVCGen(ss + cont, context, bcont) by {
            assert Seq(ss).ValidCalls();
            // decreases
            SeqFunConcatLemmas(ss, cont);
            // SeqVariablesDistinct
            SeqVariablesDistinctSeq(ss, cont, context.incarnation.Keys);
          }
          forall md: M.Model, st: State | 
            && SeqIsSafe(s, md)
            && SeqHolds(VCs, md)
            && bcont.IsSafe(md)
            && context.IsSatisfiedOn(st, md)
            ensures BlockSem(s, bcont, context.AdjustState(st), AllStates, md) 
          {
            SeqIsSafeSeq(ss, cont, md);
            Omni.SeqLemma(ss, cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates, md), md);
          }
        case Choice(ss0, ss1) =>
          var VCs0 := SeqVCGen([ss0] + cont, context, bcont) by {
            assert Choice(ss0, ss1).ValidCalls();
            // SeqVariablesDistinct
            SeqVariablesDistinctChoice(ss0, ss1, cont, context.incarnation.Keys);
            // VariablesDistinct
            // bcont.VariablesDistinctDisjointTransitivity(context.incarnation.Keys, SeqBVars([ss0] + cont), SeqBVars(s));
          }
          var VCs1 := SeqVCGen([ss1] + cont, context, bcont) by {
            assert Choice(ss0, ss1).ValidCalls();
            // SeqVariablesDistinct
            SeqVariablesDistinctChoice(ss0, ss1, cont, context.incarnation.Keys);
            // VariablesDistinct
            // bcont.VariablesDistinctDisjointTransitivity(context.incarnation.Keys, SeqBVars([ss1] + cont), SeqBVars(s));
          }
          VCs := VCs0 + VCs1;
          forall md: M.Model, st: State | 
            && SeqIsSafe(s, md)
            && SeqHolds(VCs, md)
            && bcont.IsSafe(md)
            && context.IsSatisfiedOn(st, md)
            ensures BlockSem(s, bcont, context.AdjustState(st), AllStates, md) 
          { 
            ChoiceIsSafe(ss0, ss1, cont, md);
            assert SeqHolds(VCs0, md);
            assert SeqHolds(VCs1, md);
          }
        case NewScope(vars, body) =>
          var vsNew, context' := context.AddVarSet(vars);
          assert vsNew.Values !! context.incarnation.Keys by {
            assert NewScope(vars, body) in [NewScope(vars, body)] + cont;
            assert NewScope(vars, body).VariablesDistinct(context.incarnation.Keys);
          }
          VCs := SeqVCGen([body], context', bcont.Update(cont, vars)) by {
            // decreases
            bcont.UpdateSize(cont, vars);
            assert SeqSize([body]) == body.Size();
            // ValidCalls
            assert NewScope(vars, body).ValidCalls();
            // SeqVariablesDistinct
            SeqVariablesDistinctUnion([body], context'.incarnation.Keys, vars) by {
              SeqVariablesDistinctNewScope(body, vars, cont, context.incarnation.Keys);
            }
            // VariablesDistinct
            assert bcont.Update(cont, vars).VariablesDistinct(context'.incarnation.Keys) by {
              reveal bcont.Update(cont, vars).VariablesDistinct;
            }
          }
          forall md: M.Model, st: State | 
            && SeqIsSafe(s, md)
            && SeqHolds(VCs, md)
            && bcont.IsSafe(md)
            && context.IsSatisfiedOn(st, md)
            ensures BlockSem(s, bcont, context.AdjustState(st), AllStates, md) 
          {
            NewScopeIsSafe(vars, body, cont, md);
            var blockWP := BlockWPSeq(bcont, AllStates, md);
            var contWP := Omni.SeqWP(cont, blockWP, md);
            var updWP := ([contWP] + blockWP.UpdateHead(contWP)).Update(vars);
            assert Omni.Sem(NewScope(vars, body), context.AdjustState(st), blockWP.UpdateHead(contWP), md) by {
              forall vs: State | vs.Keys == vars
                ensures Omni.Sem(body, context.AdjustState(st).Update(vs as map), blockWP.UpdateHead(contWP).UpdateAndAdd(vars), md) {
                var st' := st + vs;
                assert context'.IsSatisfiedOn(st', md) by {
                  forall e: Expr | e in context.ctx && e.HoldsOn(st, md) {
                    e.EvalFVarsLemma(st, st', md);
                  }
                }
                calc {
                  Omni.SeqSem([body], context'.AdjustState(st'), updWP, md);
                  { assert context.AdjustState(st).Update(vs as map) == context'.AdjustState(st'); }
                  Omni.SeqSem([body], context.AdjustState(st).Update(vs as map), updWP, md);
                ==> { Omni.SeqSemSingle(body, context.AdjustState(st).Update(vs as map), updWP, md); }
                  Omni.Sem(body, context.AdjustState(st).Update(vs as map), updWP, md);
                }
              }
            }
            Omni.SemNest(NewScope(vars, body), cont, context.AdjustState(st), blockWP, md);
          }
        case Escape(l) => 
          var bcont' := bcont.Update(cont, {});
          var varsToDelete := bcont'.VarsInScope(l);
          var context' := context.Delete(varsToDelete) by {
            bcont'.VarsInScopeLeqAll(l);
          }
          VCs := SeqVCGen([], context', bcont'[l..]) by {
            // decreases
            bcont'.SizePrefix(l);
            // IsDefinedOn
            assert bcont'[l..].IsDefinedOn(context'.incarnation.Keys) by {
              if l != 0 {
                assert bcont'[l..] == bcont[l - 1..] by {
                  assert bcont' == [Block.Point(cont, {} as set<Variable>)] + bcont;
                }
                assert context'.incarnation.Keys == context.incarnation.Keys - varsToDelete;
                bcont.VarsInScopeSuffix(l - 1);
                assert varsToDelete == bcont[..l - 1].AllVarsInScope();
                bcont.VariablesDistinctPrefix(context.incarnation.Keys, l - 1);
              } else {
                assert forall vs: set<Variable> :: vs - {} == vs;
              }
            }
            // JumpsDefined
            assert bcont'[l..].JumpsDefined() && bcont'[l..].VarsDefined(context'.incarnation.Keys) by {
              if l != 0 {
                assert bcont'[l..] == bcont[l - 1..];
                assert context'.incarnation.Keys == context.incarnation.Keys - varsToDelete;
                bcont.VarsInScopeSuffix(l - 1);
                assert varsToDelete == bcont[..l - 1].AllVarsInScope();
                bcont.DefinedPrefix(l - 1, context.incarnation.Keys);
              } else {
                assert forall vs: set<Variable> :: vs - {} == vs;
              }
            }
            assert bcont'[l..].VariablesDistinct(context'.incarnation.Keys) by {
             if l != 0 {
                assert bcont'[l..] == bcont[l - 1..];
                assert context'.incarnation.Keys == context.incarnation.Keys - varsToDelete;
                bcont.VarsInScopeSuffix(l - 1);
                assert varsToDelete == bcont[..l - 1].AllVarsInScope();
                bcont.VariablesDistinctPrefix(context.incarnation.Keys, l - 1);
              } else {
                calc {
                  bcont'[l..].VariablesDistinct(context'.incarnation.Keys);
                  { assert context.incarnation.Keys - {} == context.incarnation.Keys; }
                  bcont'.VariablesDistinct(context.incarnation.Keys);
                  { reveal bcont'.VariablesDistinct;
                    assert context.incarnation.Keys - {} == context.incarnation.Keys;
                    assert bcont'[1..] == bcont; }
                  true;
                }
              }
            }
          }
          forall md: M.Model, st: State | 
            && SeqHolds(VCs, md)
            && bcont.IsSafe(md)
            && SeqIsSafe(s, md)
            && context.IsSatisfiedOn(st, md)
            ensures Omni.SeqSem([Escape(l)] + cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates, md), md) 
          {
            assert bcont'[l..].IsSafe(md);
            Omni.SemNest(Escape(l), cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates, md), md) by {
              var blockWP := BlockWPSeq(bcont, AllStates, md);
              var updBlockWP := blockWP.UpdateHead(Omni.SeqWP(cont, blockWP, md));
              calc {
                context.AdjustState(st) in updBlockWP[l];
                { if l != 0 { BlockWPSeqIdx(bcont, l - 1, md); }
                  assert UpdateSet(bcont'.VarsInScope(l), BlockWPSeq(bcont'[l..], AllStates, md)[0]) == updBlockWP[l] by {
                  if l != 0 {
                    // calc {
                    //   updBlockWP[l];
                    //   ==
                    //   blockWP[l];
                      BlockWPSeqIdx(bcont, l - 1, md);
                      // UpdateSet(bcont.VarsInScope(l - 1), BlockWPSeq(bcont[l - 1..], AllStates, md)[0]);
                      assert bcont.VarsInScope(l - 1) == bcont'.VarsInScope(l) by {
                            bcont.VarsInScopeSuffix(l - 1); bcont'.VarsInScopeSuffix(l); }
                      // UpdateSet(bcont'.VarsInScope(l), BlockWPSeq(bcont'[l..], AllStates, md)[0]);
                    // }
                  } else {
                    assert forall st: State :: st.Without({}) == st;
                  } 
                } }
                context.AdjustState(st) in UpdateSet(bcont'.VarsInScope(l), BlockWPSeq(bcont'[l..], AllStates, md)[0]);
                context.AdjustState(st).Without(bcont'.VarsInScope(l)) in BlockWPSeq(bcont'[l..], AllStates, md)[0];
                { assert context'.AdjustState(st) == context.AdjustState(st).Without(bcont'.VarsInScope(l)); }
                context'.AdjustState(st) in BlockWPSeq(bcont'[l..], AllStates, md)[0];
                { assert context'.IsSatisfiedOn(st, md) by {
                  forall i | i in context'.incarnation.Values ensures i in st.Keys {
                    assert i in context.incarnation.Values;
                } } }
                true;
              }
            }
          }
        case Loop(inv, body) =>
          var VCInvIni := context.MkEntailment(inv);
          var assnvars := AssignmentTarget.Process(body) by {
            assert Loop(inv, body).ValidCalls();
          }

          var vsNew, context' := context.AddVarSet(assnvars);

          var VCInvLoop := SeqVCGen([Assume(inv), body, Check(inv), Assume(BConst(false))], context', bcont) by {
            // decreases
            calc {
              SeqSize([Assume(inv), body, Check(inv), Assume(BConst(false))]);
            == 
              1 + SeqSize([body, Check(inv), Assume(BConst(false))]);
            ==
              1 + body.Size() + SeqSize([Check(inv), Assume(BConst(false))]);
            == 
              1 + body.Size() + 1 + SeqSize([Assume(BConst(false))]);
            == 
              1 + body.Size() + 1 + 1 + SeqSize([]);
            }
            // ValidCalls
            assert Loop(inv, body).ValidCalls();
            // IsDefinedOn
            IsDefinedLoop(inv, body, context'.incarnation.Keys, |bcont|);
            // VarsDefined
            assert bcont.VarsDefined(context'.incarnation.Keys) by {
              assert context'.incarnation.Keys == context.incarnation.Keys;
            }
            // VariablesDistinct
            assert bcont.VariablesDistinct(context'.incarnation.Keys) by {
              assert context'.incarnation.Keys == context.incarnation.Keys;
            }
            // SeqVariablesDistinct
            assert SeqVariablesDistinct([Assume(inv), body, Check(inv), Assume(BConst(false))], context'.incarnation.Keys) by {
              assert context'.incarnation.Keys == context.incarnation.Keys;
              SeqVariablesDistinctLoop(body, inv, cont, context.incarnation.Keys);
            }
          }
          VCs := [VCInvIni] + VCInvLoop;
          forall md: M.Model, st: State | 
            && SeqIsSafe(s, md)
            && SeqHolds(VCs, md)
            && context.IsSatisfiedOn(st, md)
            && bcont.IsSafe(md)
            ensures Omni.SeqSem([Loop(inv, body)] + cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates, md), md) 
          {
            LoopIsSafe(inv, body, cont, md);
            forall st: State | context.IsSatisfiedOn(st, md)
              ensures Omni.SeqSem([Loop(inv, body)] + cont, context.AdjustState(st), BlockWPSeq(bcont, AllStates, md), md) {
              var inv'' := (inv.Sem(md) * context.AdjustState(st).EqExcept(assnvars));
              var inv' := inv'' * iset st': State | context.incarnation.Keys <= st'.Keys;
              var stt := context.AdjustState(st);
              Omni.SemLoopWithCont(inv, body, cont, stt, BlockWPSeq(bcont, AllStates, md), inv', md) by {
                assert stt in inv.Sem(md) by {
                  context.MkEntailmentLemma(inv, st, md);
                }

                forall st': State | st' in inv'
                  ensures Omni.Sem(body, st', BlockWPSeq(bcont, AllStates, md).UpdateHead(inv'), md) {
                  var st'' := st + map v | v in vsNew.Keys :: st'[vsNew[v]];
                  
                  assert st' == context'.AdjustState(st'');

                  assert context'.IsSatisfiedOn(st'', md) by {
                    forall e <- context'.ctx 
                      ensures e.HoldsOn(st'', md) {
                      e.EvalFVarsLemma(st, st'', md);
                    }
                  }
                  calc {
                    Omni.Sem(body, st', BlockWPSeq(bcont, AllStates, md).UpdateHead(inv'), md);
                    { SeqVariablesDistinctLoop(body, inv, cont, context.incarnation.Keys);
                      Omni.SemFrameFirst(body, st', BlockWPSeq(bcont, AllStates, md), inv'', md, context.incarnation.Keys); }
                    Omni.Sem(body, st', BlockWPSeq(bcont, AllStates, md).UpdateHead(inv''), md);
                    { AssignmentTarget.Correct(body, st', context.AdjustState(st), assnvars, BlockWPSeq(bcont, AllStates, md), inv.Sem(md), md); }
                    Omni.Sem(body, st', BlockWPSeq(bcont, AllStates, md).UpdateHead(inv.Sem(md)), md);
                    { Omni.InvSem(inv, body, st', BlockWPSeq(bcont, AllStates, md), Assume(BConst(false)), md); }
                    Omni.SeqSem([Assume(inv), body, Check(inv), Assume(BConst(false))], st', BlockWPSeq(bcont, AllStates, md), md);
                    { assert SeqHolds(VCInvLoop, md); }
                    true;
                  }
                }
              }
            }
          }
      }
    }
  }

  method VCGenProc(proc: Procedure) returns (VCs: seq<Expr>) 
    requires proc.Valid()
    ensures forall md: M.Model ::
      proc.IsSafe(md) ==>
      (forall e <- VCs :: e.Holds(md)) ==> Omni.ProcedureIsSound(proc, md)
  {
    var context := mkInitialContext(proc);
    var bcont: Block.Continuation := [Block.Point(proc.PostCheck(), {})];
    if proc.Body.Some? {
      VCs := SeqVCGen([proc.Body.value], context, bcont) by {
        assert context.incarnation.Keys == proc.ParametersKeys();
        calc {
          bcont.VariablesDistinct(context.incarnation.Keys);
          { assert context.incarnation.Keys == proc.ParametersKeys(); }
          bcont.VariablesDistinct(proc.ParametersKeys());
          { assert proc.ParametersKeys() - {} == proc.ParametersKeys();
            reveal bcont.VariablesDistinct; }
          SeqVariablesDistinct(proc.PostCheck(), proc.ParametersKeys());
          true;
        }
      }
      forall md: M.Model, st: State | 
        && SeqHolds(VCs, md)
        && proc.IsSafe(md)
        && st in proc.PreSet(md)
        ensures Omni.Sem(proc.Body.value, st, [proc.PostSet(md)], md) 
      {
        proc.IsSafePostCheckLemma(md);
        assert context.IsSatisfiedOn(st, md);
        assert Omni.Sem(proc.Body.value, context.AdjustState(st), BlockWPSeq(bcont, AllStates, md), md) by {
          Omni.SeqSemSingle(proc.Body.value, context.AdjustState(st), BlockWPSeq(bcont, AllStates, md), md);
        }
        var wpSeq: Omni.Continuation := [Omni.SeqWP(proc.PostCheck(), [AllStates], md), Omni.SeqWP(proc.PostCheck(), [AllStates], md)];
        assert BlockWPSeq(bcont, AllStates, md) == wpSeq by {
          wpSeq.Update0();
        }
        Omni.SemConsDepthLemma(proc.Body.value, context.AdjustState(st), wpSeq, [proc.PostSet(md)], 0, md) by {
          forall st: State | Omni.SeqSem(proc.PostCheck(), st, [AllStates], md)
            ensures st in proc.PostSet(md) {
            Omni.SemPostCheckLemma(proc, st, [AllStates], md);
          }
        }
        assert context.AdjustState(st) == st;
      }
    } else {
      VCs := [];
    }
  }

// /*  
//   e.HoldsWithAxiom(axioms) <==> "pick a A <= axioms", A => e

//    + requires Axioms.Holds()
//    ensures (forall e <- VCs :: e.HoldsAxioms(axioms)) ==> 
//       forall proc <- procs :: Omni.RefProcedureIsSound(proc)
//  */

  method VCGenProcs(procs: seq<Procedure>, funcs: seq<Function>) returns (VCs: seq<Expr>)
    requires forall proc <- procs :: proc.Valid()

    requires forall proc <- procs :: proc.ProceduresCalled() <= SetOfSeq(procs)
    requires forall func <- funcs :: func.FunctionsCalled() <= SetOfSeq(funcs)
    requires forall proc <- procs :: proc.FunctionsCalled() <= SetOfSeq(funcs)
    requires SeqSafeWith(procs, SetOfSeq(funcs))
    ensures 
      SeqRefHoldsWith(VCs, SetOfSeq(funcs)) ==> 
        forall proc <- procs :: Omni.RefProcedureIsSoundWith(proc, SetOfSeq(funcs))
  {
    VCs := [];
    var VCs';
    for i := 0 to |procs| 
      invariant forall md: M.Model :: 
        ((forall proc <- procs :: proc.IsSafe(md)) &&
        SeqHolds(VCs, md)) ==> forall proc <- procs[..i] :: Omni.ProcedureIsSound(proc, md)
    {
      VCs' := VCGenProc(procs[i]) by {
        assert procs[i] in procs;
      }
      ghost var VCs'' := VCs;
      VCs := VCs' + VCs;
      forall md: M.Model | 
        && (forall proc <- procs :: proc.IsSafe(md))
        && SeqHolds(VCs, md)
        ensures forall proc <- procs[..i + 1] :: Omni.ProcedureIsSound(proc, md)
      {
        assert SeqHolds(VCs', md);
        assert SeqHolds(VCs'', md);
        assert forall proc: Procedure | proc in procs[..i + 1] :: proc.IsSafe(md);
      }
    }
    if SeqRefHoldsWith(VCs, SetOfSeq(funcs)) {
      forall md: M.Model {:trigger} |
        (forall func <- funcs :: func.IsSound(md)) 
        ensures forall proc <- procs :: Omni.RefProcedureIsSound(proc, md) {
        assert SeqRefHolds(VCs, md);
        forall e <- VCs, st: State | e.IsDefinedOn(st.Keys) 
          ensures e.HoldsOn(st, md) {
          e.EvalComplete(st, iset{md.True()}, md);
        }
        assert SeqHolds(VCs, md);
        Omni.SemSoundProcs(SetOfSeq(procs), SetOfSeq(funcs), md);
      }
    }
  }
}