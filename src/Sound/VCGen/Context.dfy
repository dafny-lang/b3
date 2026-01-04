module Context {
  import opened Utils
  import M = Model
  import opened AST
  import opened State
  import opened Expr

  datatype Context = Context(
    ctx: seq<Expr>,
    incarnation: map<Variable, Variable>) 
  {
    ghost function Models(md: M.Model) : iset<State> { iset st: State | IsSatisfiedOn(st, md) }

    ghost function AdjustedModels(md: M.Model) : iset<State> { 
      iset st: State | exists st' <- Models(md) {:InAdjustedModelsLemma(st', md)} :: AdjustState(st') == st
    }

    lemma InAdjustedModelsLemma(st: State, st': State, md: M.Model)
//       requires IsSatisfiedOn(st', md)
//       requires st == AdjustState(st')
//       ensures st in AdjustedModels(md)
//     {

//     }

    function FVars(): set<Variable> 
    {
      SeqExprFVars(ctx) + incarnation.Values
    }

    function FreshVarSet(typ: Type, vars: set<Variable>): Variable
      ensures FreshVarSet(typ, vars) !in incarnation.Values
      ensures FreshVarSet(typ, vars) !in SeqExprFVars(ctx)
      ensures FreshVarSet(typ, vars) !in vars
      ensures forall c <- ctx :: FreshVarSet(typ, vars) !in c.FVars()
      ensures FreshVarSet(typ, vars).typ == typ

    function FreshVar(typ: Type): Variable
      ensures FreshVar(typ) !in incarnation.Values
      ensures FreshVar(typ) !in SeqExprFVars(ctx)
      ensures forall c <- ctx :: FreshVar(typ) !in c.FVars()
      ensures FreshVar(typ).typ == typ
    {
      FreshVarSet(typ, {})
    }

    function AdjustState(s: State): State
      requires incarnation.Values <= s.Keys
    {
      map v | v in incarnation.Keys :: s[incarnation[v]]
    }

    function AdjustStateBVars(s: State, bVars: set<Variable>): State
      requires incarnation.Values <= s.Keys + bVars
    {
      map v | v in incarnation.Keys && incarnation[v] !in bVars :: 
        s[incarnation[v]]
    }

    function UpdateIncarnation(v: Variable, x: Variable): Context
    {
      Context(ctx, incarnation[v := x])
    }

    /*
      incr = map[u -> v]

      let v := .. in v + u
    */

    function Substitute(e: Expr): Expr
      requires e.IsDefinedOn(incarnation.Keys)
      decreases e
    {
      match e
      case BConst(bvalue) => e
      case IConst(ivalue) => e
      case CustomConst(value) => e
      case BVar(v) => BVar(incarnation[v])
      case OperatorExpr(op, args) => OperatorExpr(op, SeqSubstitute(args))
      case FunctionCallExpr(func, args) => FunctionCallExpr(func, SeqSubstitute(args))
      case LetExpr(v, rhs, body) => 
        var v' := v.FreshVar(incarnation.Values);
        LetExpr(v', Substitute(rhs), UpdateIncarnation(v, v').Substitute(body))
      case QuantifierExpr(univ, v, body) => 
        var v' := v.FreshVar(incarnation.Values);
        QuantifierExpr(univ, v', UpdateIncarnation(v, v').Substitute(body))
    }

    function SeqSubstitute(ss: seq<Expr>): seq<Expr>
      requires SeqExprFVars(ss) <= incarnation.Keys
      ensures |SeqSubstitute(ss)| == |ss|
      decreases ss
    {
      if ss == [] then [] else
      [Substitute(ss[0])] + SeqSubstitute(ss[1..])
    }

    function MkEntailment(e: Expr): Expr
      requires e.IsDefinedOn(incarnation.Keys)
    {
      Implies(Conj(ctx), Substitute(e))
    }

    function MkEntailmentSeq(ss: seq<Expr>): seq<Expr>
      requires SeqExprFVars(ss) <= incarnation.Keys
    {
      seq(|ss|, (i: nat) requires i < |ss| => 
        SeqExprFVarsLemma(ss, ss[i]);
        MkEntailment(ss[i]))
    }

    lemma MkEntailmentSeqLemma(ss: seq<Expr>, e: Expr)
      requires SeqExprFVars(ss) <= incarnation.Keys
      requires e in ss
      ensures forall e <- ss :: e.IsDefinedOn(incarnation.Keys)
      ensures MkEntailment(e) in MkEntailmentSeq(ss)
    {
      forall e <- ss { SeqExprFVarsLemma(ss, e); }
      assert MkEntailment(e) == MkEntailmentSeq(ss)[Index(ss, e)];
    }

    ghost predicate IsDefinedOn(d: set<Variable>)
    {
      forall e <- ctx :: e.IsDefinedOn(d)
    }

    /*
    
    */
    ghost predicate IsSatisfiedOn(s: State, md: M.Model) 
    {
      && IsDefinedOn(s.Keys)
      && incarnation.Values <= s.Keys
      && (forall e <- ctx :: e.HoldsOn(s, md))
    }

    lemma  SubstituteIsDefinedOnLemma(e: Expr, d: set<Variable>)
      requires e.IsDefinedOn(incarnation.Keys)
      requires incarnation.Values <= d
      ensures Substitute(e).IsDefinedOn(d)
      decreases e
    {
      match e
      case BVar(v) => 
        if v in incarnation.Keys { assert incarnation[v] in incarnation.Values; }
      case OperatorExpr(op, args) =>
        SeqSubstituteIsDefinedOnLemma(args, d);
      case FunctionCallExpr(func, args) =>
        SeqSubstituteIsDefinedOnLemma(args, d);
      case LetExpr(v, rhs, body) =>
        var v' := v.FreshVar(incarnation.Values);
        calc {
          Substitute(e).FVars();
          == 
          Substitute(rhs).FVars() + (UpdateIncarnation(v, v').Substitute(body).FVars() - {v'});
          <= { UpdateIncarnation(v, v').SubstituteIsDefinedOnLemma(body, d + {v'}); }
          d + (d + {v'} - {v'});
        }
      case QuantifierExpr(univ, v, body) =>
        var v' := v.FreshVar(incarnation.Values);
        calc {
          Substitute(e).FVars();
          == 
          UpdateIncarnation(v, v').Substitute(body).FVars() - {v'};
          <= { UpdateIncarnation(v, v').SubstituteIsDefinedOnLemma(body, d + {v'}); }
          d;
        }
      case _ =>
    }

    lemma SeqSubstituteIsDefinedOnLemma(ss: seq<Expr>, d: set<Variable>)
      requires SeqExprFVars(ss) <= incarnation.Keys
      requires incarnation.Values <= d
      ensures forall e <- SeqSubstitute(ss) :: e.IsDefinedOn(d)
      ensures SeqExprFVars(SeqSubstitute(ss)) <= d
      decreases ss
    {
      if ss != [] {
        SubstituteIsDefinedOnLemma(ss[0], d);
        SeqSubstituteIsDefinedOnLemma(ss[1..], d);
      }
    }

    lemma ForallPush(s1: State, s2: State, e1: Expr, e2: Expr, v: Variable, md: M.Model)
      requires e1.IsDefinedOn(s1.Keys + {v})
      requires e2.IsDefinedOn(s2.Keys + {v})
      requires forall b: M.Any | md.HasType(b, v.typ.ToType()) :: e1.Eval(s1.UpdateAt(v, b), md) == e2.Eval(s2.UpdateAt(v, b), md)
      ensures (forall b: M.Any | md.HasType(b, v.typ.ToType()) :: e1.HoldsOn(s1.UpdateAt(v, b), md)) == (forall b: M.Any | md.HasType(b, v.typ.ToType()) :: e2.HoldsOn(s2.UpdateAt(v, b), md))
      ensures (forall b: M.Any | md.HasType(b, v.typ.ToType()) :: SomeBVal?(e1.Eval(s1.UpdateAt(v, b), md), md)) == (forall b: M.Any | md.HasType(b, v.typ.ToType()) :: SomeBVal?(e2.Eval(s2.UpdateAt(v, b), md), md))
    {  }

    lemma ExistsPush(s1: State, s2: State, e1: Expr, e2: Expr, v: Variable, md: M.Model)
      requires e1.IsDefinedOn(s1.Keys + {v})
      requires e2.IsDefinedOn(s2.Keys + {v})
      requires forall b: M.Any | md.HasType(b, v.typ.ToType()) :: e1.HoldsOn(s1.UpdateAt(v, b), md) == e2.HoldsOn(s2.UpdateAt(v, b), md)
      ensures (exists b: M.Any | md.HasType(b, v.typ.ToType()) :: e1.HoldsOn(s1.UpdateAt(v, b), md)) == (exists b: M.Any | md.HasType(b, v.typ.ToType()) :: e2.HoldsOn(s2.UpdateAt(v, b), md))
    {  }

    lemma SeqAdjustStateSubstituteLemma(ss: seq<Expr>, s: State, md: M.Model)
      requires SeqExprFVars(ss) <= incarnation.Keys
      requires incarnation.Values <= s.Keys
      ensures
        (SeqSubstituteIsDefinedOnLemma(ss, s.Keys);
         SeqEval(ss, AdjustState(s), md) == 
         SeqEval(SeqSubstitute(ss), s, md))
      decreases ss
    {
      if ss != [] {
        SeqAdjustStateSubstituteLemma(ss[1..], s, md);
        SeqSubstituteIsDefinedOnLemma(ss, s.Keys);
        AdjustStateSubstituteLemma(s, ss[0], md);
      }
    }


    lemma AdjustStateSubstituteLemma(s: State, e: Expr, md: M.Model)
      requires e.IsDefinedOn(incarnation.Keys)
      requires incarnation.Values <= s.Keys
      ensures (SubstituteIsDefinedOnLemma(e, s.Keys);
        e.Eval(AdjustState(s), md)) == Substitute(e).Eval(s, md)
      decreases e
    {
      match e
      case OperatorExpr(op, args) =>
        SeqAdjustStateSubstituteLemma(args, s, md);
      case FunctionCallExpr(func, args) =>
        SeqAdjustStateSubstituteLemma(args, s, md);
      case QuantifierExpr(univ, v, body) => 
        var v' := v.FreshVar(incarnation.Values);
        SubstituteIsDefinedOnLemma(e, s.Keys);
        forall b: M.Any | md.HasType(b, v.typ.ToType()) 
          ensures body.Eval(AdjustState(s).UpdateAt(v, b), md) == UpdateIncarnation(v, v').Substitute(body).Eval(s.UpdateAt(v', b), md) {
          calc {
            UpdateIncarnation(v, v').Substitute(body).Eval(s.UpdateAt(v', b), md);
            == { UpdateIncarnation(v, v').AdjustStateSubstituteLemma(s.UpdateAt(v', b), body, md); }
            body.Eval(UpdateIncarnation(v, v').AdjustState(s.UpdateAt(v', b)), md);
            == { body.EvalFVarsLemma(AdjustState(s).UpdateAt(v, b), UpdateIncarnation(v, v').AdjustState(s.UpdateAt(v', b)), md); }
            body.Eval(AdjustState(s).UpdateAt(v, b), md);
          }
        }
      case BVar(v) => if v in incarnation.Keys { assert incarnation[v] in incarnation.Values; }
      case LetExpr(v, rhs, body) =>
        var v' := v.FreshVar(incarnation.Values);
        var b := Substitute(rhs).Eval(s, md) by {
          SubstituteIsDefinedOnLemma(rhs, s.Keys);
        }
        if b.Some? {
          var b := b.value;
          SubstituteIsDefinedOnLemma(e, s.Keys);
          calc {
            Substitute(e).Eval(s, md);
            ==
            LetExpr(v', Substitute(rhs), UpdateIncarnation(v, v').Substitute(body)).Eval(s, md);
            ==
            UpdateIncarnation(v, v').Substitute(body).Eval(s.UpdateAt(v', b), md);
            == { UpdateIncarnation(v, v').AdjustStateSubstituteLemma(s.UpdateAt(v', b), body, md); }
            body.Eval(UpdateIncarnation(v, v').AdjustState(s.UpdateAt(v', b)), md);
            == { body.EvalFVarsLemma(AdjustState(s).UpdateAt(v, b), UpdateIncarnation(v, v').AdjustState(s.UpdateAt(v', b)), md); }
            body.Eval(AdjustState(s).UpdateAt(v, b), md);
          }
        }
      case _  => 
    }

//     lemma AdjustStateSubstituteLemma(s: State, e: Expr, md: M.Model)
//       requires e.IsDefinedOn(|incarnation|)
//       requires forall ic <- incarnation :: ic < |s|
//       ensures Substitute(e).IsDefinedOn(|s|)
//       ensures e.HoldsOn(AdjustState(s), md) == Substitute(e).HoldsOn(s, md)
//     {
//       SubstituteIsDefinedOnLemma(e, |s|);
//       AdjustStateSubstituteIdxLemma(s, e, 0, md);
//       assert [] + AdjustState(s) == AdjustState(s);
//     }
//   }

    lemma MkEntailmentLemma(e: Expr, st: State, md: M.Model)
      requires e.IsDefinedOn(incarnation.Keys)
      requires incarnation.Values <= st.Keys
      requires IsSatisfiedOn(st, md)
      requires MkEntailment(e).Holds(md)
      ensures e.HoldsOn(AdjustState(st), md)
    {
      assert Implies(Conj(ctx), Substitute(e)).IsDefinedOn(st.Keys) by {
        IsDefinedOnImpliesLemma(Conj(ctx), Substitute(e), st) by {
          EvalConjLemma(ctx, st, md);
          SubstituteIsDefinedOnLemma(e, st.Keys);
        }
      }
      assert e.HoldsOn(AdjustState(st), md) by { 
        calc {
          e.HoldsOn(AdjustState(st), md);
          { SubstituteIsDefinedOnLemma(e, st.Keys);
            AdjustStateSubstituteLemma(st, e, md); }
          Substitute(e).HoldsOn(st, md);
          { EvalConjLemma(ctx, st, md);
            AdjustStateSubstituteLemma(st, e, md);
            HoldsOnImpliesLemma(Conj(ctx), Substitute(e), st, md); }
          MkEntailment(e).Holds(md);
        }
      }
    }

    function Add(e: Expr): Context
      requires e.IsDefinedOn(incarnation.Keys)
    {
      this.(ctx := ctx + [Substitute(e)])
    }

//     function SeqSubstitute(ss: seq<Expr>): seq<Expr>
//       requires forall e <- ss :: e.IsDefinedOn(|incarnation|)
//     {
//       seq(|ss|, (i: nat) requires i < |ss| => Substitute(ss[i]))
//     }

    lemma GetSeqSubstituteLemma(ss: seq<Expr>, e: Expr) returns (e': Expr) 
      requires SeqExprFVars(ss) <= incarnation.Keys
      requires e in SeqSubstitute(ss)
      ensures e' in ss
      ensures e'.IsDefinedOn(incarnation.Keys)
      ensures Substitute(e') == e
    {
      if ss != [] {
        if Substitute(ss[0]) == e {
          e' := ss[0];
        } else {
          e' := GetSeqSubstituteLemma(ss[1..], e);
        }
      }
    }

    function AddSeq(ss: seq<Expr>): Context
      requires SeqExprFVars(ss) <= incarnation.Keys
    {
      this.(ctx := ctx + SeqSubstitute(ss))
    }

    function mkPreContext(proc: Procedure, args: CallArguments): Context
      requires Call(proc, args).ValidCalls()
      requires args.IsDefinedOn(incarnation.Keys)
      ensures mkPreContext(proc, args).incarnation.Keys == args.FVars()
      ensures forall i <- mkPreContext(proc, args).incarnation.Values :: i in incarnation.Values
    {
      var incrPre := map v | v in args.FVars() :: incarnation[v];
      Context(ctx, incrPre)
    }

    lemma mkPreContextLemma(proc: Procedure, args: CallArguments, s: State)
      requires Call(proc, args).ValidCalls()
      requires args.IsDefinedOn(incarnation.Keys)
      requires incarnation.Values <= s.Keys
      ensures mkPreContext(proc, args).AdjustState(s) == args.Eval(AdjustState(s))
    {
      forall v | v in args.FVars()
        ensures (mkPreContext(proc, args).AdjustState(s))[v] == args.Eval(AdjustState(s))[v]
      {
        assert incarnation[v] in incarnation.Values;
        assert s[incarnation[v]] == args.Eval(AdjustState(s))[v];
      }
    }

    function mkPostContext(proc: Procedure, args: CallArguments/*, oldContext: Context*/): Context
      requires Call(proc, args).ValidCalls()
      requires args.IsDefinedOn(incarnation.Keys)
      // requires args.IsDefinedOn(oldContext.incarnation.Keys)
      // requires |oldContext.incarnation| >= args.NumInOutArgs()
      ensures mkPostContext(proc, args/*, oldContext*/).incarnation.Keys == args.FVars() /*+ args.NumInOutArgs()*/
    {
      // var oldNum := args.NumInOutArgs();
      var incrPost: map<Variable, Variable> := map v | v in args.FVars() :: incarnation[v];
      // var incrPostOld: seq<Idx> := seq(args.NumInOutArgs(), (i: nat) requires i < args.NumInOutArgs() => 
      //   args.InOutArgsLemma(args.InOutArgs()[i]); 
      //   args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[i]), |oldContext.incarnation|);
      //   oldContext.incarnation[args.InOutArgs()[i]]);
      Context(ctx, incrPost /*+ incrPostOld*/)
    }

    lemma mkPostContextIncrSubsetLemma(proc: Procedure, args: CallArguments,/* oldContext: Context,*/ v: Variable)
      requires Call(proc, args).ValidCalls()
      requires args.IsDefinedOn(incarnation.Keys)
      // requires args.IsDefinedOn(|oldContext.incarnation|)
      // requires |oldContext.incarnation| >= args.NumInOutArgs()
      requires v in mkPostContext(proc, args/*, oldContext*/).incarnation.Values
      ensures /*i in oldContext.incarnation ||*/ v in incarnation.Values
    {
      // var oldNum := args.NumInOutArgs();
      // var incrPost: seq<Idx> := seq(|args|, (i: nat) requires i < |args| => 
      //   args.IsDefinedOnIn(args[i], |incarnation|);
      //   incarnation[args[i].v]); 
      // var incrPostOld: seq<Idx> := seq(args.NumInOutArgs(), (i: nat) requires i < args.NumInOutArgs() => 
      //   args.InOutArgsLemma(args.InOutArgs()[i]); 
      //   args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[i]), |oldContext.incarnation|);
      //   oldContext.incarnation[args.InOutArgs()[i]]);
      // assert incrPost + incrPostOld == mkPostContext(proc, args, oldContext).incarnation;
      // assert i in incrPost + incrPostOld;
      // if i in incrPost {
      //   assert i == incrPost[Index(incrPost, i)];
      //   args.IsDefinedOnIn(args[Index(incrPost, i)], |incarnation|);
      //   assert i == incarnation[args[Index(incrPost, i)].v];
      // } else {
      //   assert i in incrPostOld;
      //   assert i == incrPostOld[Index(incrPostOld, i)];
      //   args.InOutArgsLemma(args.InOutArgs()[Index(incrPostOld, i)]);
      //   args.IsDefinedOnIn(InOutArgument(args.InOutArgs()[Index(incrPostOld, i)]), |oldContext.incarnation|);
      //   assert i == oldContext.incarnation[args.InOutArgs()[Index(incrPostOld, i)]];
      // }
    }

    method AddEq(v: Variable, e: Expr) returns (ghost vNew: Variable, context: Context)
      requires v in incarnation.Keys
      requires e.IsDefinedOn(incarnation.Keys)
      ensures incarnation.Keys == context.incarnation.Keys
      ensures ctx + [Eq(BVar(vNew), Substitute(e))] == context.ctx
      ensures incarnation[v := vNew] == context.incarnation
      // ensures forall i <- incarnation.Values :: i < vNew 
      ensures forall c <- ctx :: vNew !in c.FVars()
      ensures vNew !in incarnation.Values
      ensures vNew !in SeqExprFVars(ctx)
      // ensures 
    {
      var v' := FreshVar(v.typ);
      var ctx' := ctx + [Eq(BVar(v'), Substitute(e))];
      var incarnation' := incarnation[v := v'];
      context := Context(ctx', incarnation');
      vNew := v';
    }

    method AddVarSet(vars: set<Variable>) returns (ghost vsNew: map<Variable, Variable>, context: Context)
      // requires vars <= incarnation.Keys
      ensures vsNew.Values == vars
      ensures context.ctx         == ctx
      ensures context.incarnation.Keys == incarnation.Keys + vars
      ensures forall v <- vars :: context.incarnation[v] in vsNew.Keys && vsNew[context.incarnation[v]] == v
      ensures vsNew.Keys !! incarnation.Values
      ensures forall c <- ctx :: c.FVars() !! vsNew.Keys
      ensures SeqExprFVars(ctx) !! vsNew.Keys
      ensures forall v <- incarnation.Keys :: v !in vars ==> context.incarnation[v] == incarnation[v]
      ensures context.incarnation.Values <= vsNew.Keys + incarnation.Values
    {
      var vars' := vars; 
      var incr' := incarnation;
      var vs: map<Variable, Variable> := map[];
      // vNew := v';
      while vars' != {}
        invariant incr'.Keys == incarnation.Keys + (vars - vars')
        invariant vars' <= vars
        invariant forall v <- vars - vars' :: incr'[v] in vs.Keys && vs[incr'[v]] == v
        invariant vs.Keys !! incarnation.Values
        invariant forall v <- incarnation.Keys :: v !in vars - vars' ==> incr'[v] == incarnation[v]
        invariant incr'.Values <= vs.Keys + incarnation.Values
        invariant forall c <- ctx :: c.FVars() !! vs.Keys
        invariant SeqExprFVars(ctx) !! vs.Keys
        invariant vs.Values == vars - vars'
      {
        var v :| v in vars';
        vars' := vars' - {v};
        var v' := FreshVarSet(v.typ, vs.Keys);
        assert vs[v' := v].Values == vs.Values + {v} by {
          assert vs[v' := v] == vs + map[v' := v];
        }
        vs := vs[v' := v];
        incr' := incr'[v := v'];
      }
      vsNew := vs;
      context := Context(ctx, incr');
    }

    function Delete(vars: set<Variable>): Context
      requires vars <= incarnation.Keys
    {
      Context(ctx, incarnation - vars)
    }
      

    // method AddVars(n: nat) returns (ghost vNew: Idx, context: Context)
    //   // ensures incarnation <= AddVars(n).incarnation 
    //   ensures context.ctx         == ctx
    //   ensures |context.incarnation| == |incarnation| + n
    //   ensures forall i: nat :: i < n ==> context.incarnation[i] == vNew + i
    //   ensures forall i: nat :: n <= i < |incarnation| + n ==> context.incarnation[i] == incarnation[i - n]
    //   ensures forall c <- ctx :: c.Depth() < vNew
    //   ensures SeqMax(incarnation) < vNew
    //   ensures SeqExprDepth(ctx) < vNew
    // {
    //   var v := FreshIdx();
    //   var addOn := seq(n, (i: nat) => v + i);
    //   context := Context(ctx, addOn + incarnation);
    //   vNew := v;
    // }

//     // lemma SubstituteIdxIsDefinedOnLemmaOperator
  }

  function mkInitialContext(proc: Procedure): Context
  {
    var incr := map v | v in proc.ParametersKeys() :: v;
    // var incrOld := seq(proc.NumInOutArgs(), (i: nat) requires i < proc.NumInOutArgs() => 
    //   proc.InOutVarsIdxs()[i]);
    Context(proc.Pre, incr /*+ incrOld*/)
  }

//   lemma mkInitialContextLemma(proc: Procedure, i: nat)
//     requires i in mkInitialContext(proc).incarnation
//     ensures i < |proc.Parameters| + proc.NumInOutArgs()
//   {
//     var incr := seq(|proc.Parameters|, (i: nat) => i);
//     var incrOld := seq(proc.NumInOutArgs(), (i: nat) requires i < proc.NumInOutArgs() => 
//       proc.InOutVarsIdxs()[i]);
//     if i in incrOld {
//       assert i == proc.InOutVarsIdxs()[Index(incrOld, i)];
//       proc.InOutVarsIdxsLemma(proc.Parameters, 0, Index(incrOld, i));
//     }
  // }
}