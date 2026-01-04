module AST {
  import opened Std.Wrappers
  import opened Utils
  import M = Model
  import opened State
  import opened Expr

  datatype ParameterMode = In | InOut | Out

  datatype Parameter = Parameter(v: Variable, mode: ParameterMode)
  
  datatype CallArgument = CallArgument(v: Variable, mode: ParameterMode)
  {
    function OutArg(): set<Variable> {
      match this.mode
      case In => {}
      case InOut => {this.v}
      case Out => {this.v}
    }

    function IsInOutArg(): bool {
      match this.mode
      case InOut => true
      case _ => false
    }

    predicate IsDefinedOn(d: set<Variable>) {
      {this.v} <= d
    }

    function Eval(s: State): M.Any
      requires IsDefinedOn(s.Keys)
    {
      match mode
      case In => s[v]
      case InOut => s[v]
      case Out => s[v]
    }
  }

  newtype CallArguments = seq<CallArgument> {

    function OutArgs(): set<Variable> {
      if this == [] then {} else this[0].OutArg() + this[1..].OutArgs()
    }

    function NumInOutArgs(): nat {
      if this == [] then 
        0 
      else 
        if this[0].mode == InOut then 
          1 + this[1..].NumInOutArgs() 
        else this[1..].NumInOutArgs()
    }


    function InOutArgs(): seq<Variable> 
      ensures |InOutArgs()| == NumInOutArgs()
    {
      if this == [] then 
        [] else 
      if this[0].IsInOutArg() then 
        [this[0].v] + this[1..].InOutArgs() 
      else this[1..].InOutArgs()
    }

    lemma InOutArgsLemma(v: Variable)
      requires v in InOutArgs()
      ensures CallArgument(v, InOut) in this
    {

    }

    lemma OutArgsDepthLemma()
      ensures OutArgs() <= FVars()
    { }

    function FVars(): set<Variable> {
      if this == [] then {} else {this[0].v} + this[1..].FVars()
    }

    predicate IsDefinedOn(d: set<Variable>) {
      FVars() <= d
    }

    lemma IsDefinedOnIn(arg: CallArgument, d: set<Variable>)
      requires arg in this
      requires IsDefinedOn(d)
      ensures arg.IsDefinedOn(d)
    { 
      if this != [] {
        if arg != this[0] {
          this[1..].IsDefinedOnIn(arg, d);
        }
      }
    }
      
    function Eval(s: State): State 
      requires IsDefinedOn(s.Keys)
      ensures Eval(s).Keys == FVars()
    {
      map v | v in FVars() :: s[v]
    }

//     function EvalOld(s: State): State 
//       requires IsDefinedOn(|s|)
//       ensures |EvalOld(s)| == NumInOutArgs()
//     {
//       seq(NumInOutArgs(), (i: nat) requires i < NumInOutArgs() => 
//         InOutArgsLemma(InOutArgs()[i]);
//         IsDefinedOnIn(InOutArgument(InOutArgs()[i]), |s|);
//         s[InOutArgs()[i]]
//       )
//     }

//     lemma NumInOutArgsConcatLemma(args: CallArguments)
//       ensures (this + args).NumInOutArgs() == NumInOutArgs() + args.NumInOutArgs()
//       ensures (this + args).Depth() == max(this.Depth(), args.Depth())
//     {
//       if this == [] {
//         assert this + args == args;
//       } else {
//         assert (this + args)[0] == this[0];
//         assert (this + args)[1..] == this[1..] + args;
//         this[1..].NumInOutArgsConcatLemma(args);
//       }
//     }
  }

  class Procedure {
    const Name: string
    const Parameters: seq<Parameter>
    const Pre: seq<Expr>
    const Post: seq<Expr>
    var Body: Option<Stmt>

    function ParametersKeys(): set<Variable> {
      SetOfSeq(seq(|Parameters|, (i: nat) requires i < |Parameters| => Parameters[i].v))
    }

    function NumInOutArgs'(Parameters: seq<Parameter>): nat {
      if Parameters == [] then 0 else
      if Parameters[0].mode == InOut then 1 + NumInOutArgs'(Parameters[1..]) else
      NumInOutArgs'(Parameters[1..])
    }

    function NumInOutArgs(): nat {
      NumInOutArgs'(Parameters)
    }

//     predicate IsOldVar(i: Idx) 
//     {
//       |Parameters| <= i
//     }

//     function OldVars(): set<Idx> {
//       set i: Idx | IsOldVar(i) && i < |Parameters| + NumInOutArgs()
//     }


    ghost predicate InPreSet(st: State, m: M.Model) 
    {
      && ParametersKeys() /*+ NumInOutArgs()*/ == st.Keys
      /*&& (forall i: nat :: i < NumInOutArgs() ==> 
        (InOutVarsIdxsLemma(Parameters, 0, i);
         st[i + |Parameters|] == st[InOutVarsIdxs()[i]]))*/
      && forall e <- Pre :: e.IsDefinedOn(st.Keys) && e.HoldsOn(st, m)
    }

    ghost function PreSet(m: M.Model): iset<State> 
    {
      iset st: State | InPreSet(st, m)
    }

    ghost predicate InPostSet(st: State, m: M.Model) 
    {
      forall e <- Post :: e.IsDefinedOn(st.Keys) && e.HoldsOn(st, m)
    }

    ghost function PostSet(m: M.Model): iset<State> 
    {
      iset st': State | InPostSet(st', m)
    }

    function PostCheck'(p: seq<Expr>): seq<Stmt> 
      requires forall e <- p :: e.IsDefinedOn(ParametersKeys() /*+ NumInOutArgs()*/)
      ensures SeqValidCalls(PostCheck'(p))
      ensures SeqIsDefinedOn(PostCheck'(p), ParametersKeys() /*+ NumInOutArgs()*/)
      ensures SeqJumpsDefinedOn(PostCheck'(p), 0)
      ensures SeqVariablesDistinct(PostCheck'(p), ParametersKeys() /*+ NumInOutArgs()*/)
    {
      if p == [] then [] else
        assert forall e <- p[1..] :: e in p;
        assert p[0] in p;
        assert p[0].IsDefinedOn(ParametersKeys() /*+ NumInOutArgs()*/);
        assert Check(p[0]).IsDefinedOn(ParametersKeys() /*+ NumInOutArgs()*/);
        [Check(p[0])] + PostCheck'(p[1..])
    }

    function PostCheck(): seq<Stmt> 
      requires Valid()
      ensures SeqValidCalls(PostCheck())
      ensures SeqIsDefinedOn(PostCheck(), ParametersKeys() /*+ NumInOutArgs()*/)
      ensures SeqVariablesDistinct(PostCheck(), ParametersKeys() /*+ NumInOutArgs()*/)
      reads this`Body
    {
      PostCheck'(Post)
    }

//     function InOutVarsIdxs'(parameter: seq<Parameter>, idx: Idx): seq<Idx>
//       ensures |InOutVarsIdxs'(parameter, idx)| == NumInOutArgs'(parameter)
//     {
//       if parameter == [] then [] else
//       if parameter[0].mode == InOut then
//         [idx] + InOutVarsIdxs'(parameter[1..], idx + 1)
//       else
//         InOutVarsIdxs'(parameter[1..], idx + 1)
//     }

//     function InOutVarsIdxs(): seq<Idx>
//     {
//       InOutVarsIdxs'(Parameters, 0)
//     }

//     lemma InOutVarsIdxsLemma(parameter: seq<Parameter>, idx: Idx, i: nat)
//       requires i < |InOutVarsIdxs'(parameter, idx)|
//       ensures InOutVarsIdxs'(parameter, idx)[i] < |parameter| + idx
//     {
//       if parameter != [] {
//         if i != 0 {
//           InOutVarsIdxsLemma(parameter[1..], idx + 1, i - 1);
//         }
//       }
//     }

//     function InOutArgsState(st: State): State
//       requires |Parameters| <= |st|
//     {
//       seq(|InOutVarsIdxs()|, (i: nat) requires i < |InOutVarsIdxs()| => 
//         InOutVarsIdxsLemma(Parameters, 0, i);
//         st[InOutVarsIdxs()[i]])
//     }

    ghost predicate ValidBody() 
      requires Body.Some?
      reads this`Body
    {
      var body := Body.value;
      && body.ValidCalls()
      && body.IsDefinedOn(ParametersKeys() /*+ NumInOutArgs()*/)
      && body.JumpsDefinedOn(0)
      && body.VariablesDistinct(ParametersKeys() /*+ NumInOutArgs()*/)
      // && body.ImmutableVars(OldVars())
    }

    ghost predicate Valid() 
      reads this`Body
    {
      && (Body.Some? ==> ValidBody())
      && (forall e <- Pre :: e.IsDefinedOn(ParametersKeys() /*+ NumInOutArgs()*/))
      && (forall e <- Post :: e.IsDefinedOn(ParametersKeys() /*+ NumInOutArgs()*/))
    }

    function ProceduresCalled(): set<Procedure> 
      reads this`Body
    {
      if Body.Some? then Body.value.ProceduresCalled() else {}
    }

    function FunctionsCalled(): set<Function> 
      reads this`Body
    {
      if Body.Some? then Body.value.FunctionsCalled() + SeqExprFunctionsCalled(Pre) + SeqExprFunctionsCalled(Post) else {}
    }

    ghost predicate IsSafe(m: M.Model) 
      reads this`Body
    {
      && (forall e <- Pre :: e.IsSafe(m))
      && (forall e <- Post :: e.IsSafe(m))
      && (Body.Some? ==> Body.value.IsSafe(m))
    }

    lemma IsSafeLemma'(p: seq<Expr>, m: M.Model)
      requires forall e <- p :: e.IsSafe(m)
      requires forall e <- p :: e.IsDefinedOn(ParametersKeys() /*+ NumInOutArgs()*/)
      ensures SeqIsSafe(PostCheck'(p), m)
    {
      if p != [] {
        assert p[0] in p;
        IsSafeLemma'(p[1..], m) by {
          assert forall e <- p[1..] :: e in p;
        }
      }
    }

    lemma IsSafeLemma(m: M.Model)
      requires IsSafe(m)
      requires Valid()
      ensures SeqIsSafe(PostCheck(), m)
    {
      IsSafeLemma'(Post, m);
    }

    ghost predicate IsSafeWith(funs: set<Function>)
      reads *
    {
      forall md: M.Model ::
        (forall func <- funs :: func.IsSound(md)) ==> IsSafe(md)
    }

    lemma IsSafePostCheckLemma'(m: M.Model, p: seq<Expr>)
      requires forall e <- p :: e.IsSafe(m)
      requires forall e <- p :: e.IsDefinedOn(ParametersKeys() /*+ NumInOutArgs()*/)
      ensures SeqIsSafe(PostCheck'(p), m)
    {
      if p != [] {
        assert p[0] in p;
        IsSafePostCheckLemma'(m, p[1..]);
      }
    }

    lemma IsSafePostCheckLemma(m: M.Model)
      requires IsSafe(m)
      requires Valid()
      ensures SeqIsSafe(PostCheck(), m)
    {
      IsSafePostCheckLemma'(m, Post);
    }
  }

  ghost predicate SeqSafeWith(procs: seq<Procedure>, funs: set<Function>)
    reads *
  {
    forall proc <- procs :: proc.IsSafeWith(funs)
  }

  datatype Stmt =
    | Check(e: Expr)
    | Assume(e: Expr)
    | Seq(ss: seq<Stmt>)
    | Assign(lhs: Variable, rhs: Expr)
    | NewScope(vars: set<Variable>, s: Stmt)
    | Escape(l: nat)
    | Choice(0: Stmt, 1: Stmt)
    | Loop(inv: Expr, body: Stmt)
    | Call(proc: Procedure, args: CallArguments)
  {

    predicate Single() {
      match this
      case Assign(_, _) => true
      case Check(_) => true
      case Assume(_) => true
      case Call(_, _) => true
      case _ => false
    }

    ghost predicate VariablesDistinct(vars: set<Variable>)
    {
      match this
      case Seq(ss) => SeqVariablesDistinct(ss, vars)
      case Choice(s0, s1) => s0.VariablesDistinct(vars) && s1.VariablesDistinct(vars)
      case NewScope(vs, s) => vs !! vars && s.VariablesDistinct(vars + vs)
      case Loop(inv, body) => body.VariablesDistinct(vars)
      case _ => true
    }

    predicate ValidCalls() {
      match this
      case Call(proc, args) =>
        && SeqExprFVars(proc.Pre) <= args.FVars()
        && SeqExprFVars(proc.Post) <= args.FVars() /*+ args.NumInOutArgs()*/
      case Seq(ss) => forall s <- ss :: s.ValidCalls()
      case Choice(s0, s1) => s0.ValidCalls() && s1.ValidCalls()
      case NewScope(n, s) => s.ValidCalls()
      case Loop(inv, body) => body.ValidCalls()
      case _ =>
        true
    }

    function Size(): nat {
      match this
      case Check(_) => 1
      case Assume(_) => 1
      case Seq(ss) => 1 + SeqSize(ss)
      case Assign(_, _) => 1
      case Choice(s0, s1) => 1 + s0.Size() + s1.Size()
      case NewScope(n, s) => 2 + s.Size()
      case Escape(l) => 2
      case Loop(inv, body) => 4 + body.Size()
      case Call(proc, args) => 1
    }

    function FVars(): set<Variable> {
      match this
      case Check(e) => e.FVars()
      case Assume(e) => e.FVars()
      case Seq(ss) => SeqFVars(ss)
      case Assign(x, rhs) => {x} + rhs.FVars()
      case Choice(s0, s1) => s0.FVars() + s1.FVars()
      case NewScope(vars, s) => vars + s.FVars()
      case Escape(l) => {}
      case Loop(inv, body) => inv.FVars() + body.FVars()
      case Call(proc, args) => args.FVars() /*+ args.NumInOutArgs()*/
    }

    function BVars(): set<Variable> {
      match this
      case Choice(s0, s1) => s0.BVars() + s1.BVars()
      case NewScope(vars, s) => vars + s.BVars()
      case Loop(inv, body) => body.BVars()
      case Seq(ss) => SeqBVars(ss)
      case _ => {}
    }

    predicate IsDefinedOn(vars: set<Variable>) 
    {
      FVars() <= vars
    }


    function JumpDepth() : nat {
      match this
      case Check(e) => 0
      case Assume(e) => 0
      case Assign(id, rhs) => 0
      case Seq(ss) => SeqJumpDepth(ss)
      case Choice(s0, s1) => max(s0.JumpDepth(), s1.JumpDepth())
      case NewScope(n, s) => if s.JumpDepth() == 0 then 0 else s.JumpDepth() - 1
      case Escape(l) => l
      case Loop(inv, body) => body.JumpDepth()
      case Call(proc, args) => 0
    }

    predicate JumpsDefinedOn(d: nat) {
      JumpDepth() <= d
    }

    function ProceduresCalled(): set<Procedure> {
      match this
      case Call(proc, _) => {proc}
      case Seq(ss) => SeqProceduresCalled(ss)
      case Choice(s0, s1) => s0.ProceduresCalled() + s1.ProceduresCalled()
      case NewScope(_, s) => s.ProceduresCalled()
      case Loop(_, body) => body.ProceduresCalled()
      case _ => {}
    }

    function FunctionsCalled(): set<Function> {
      match this
      case Seq(ss) => SeqFunctionsCalled(ss)
      case Choice(s0, s1) => s0.FunctionsCalled() + s1.FunctionsCalled()
      case NewScope(_, s) => s.FunctionsCalled()
      case Loop(_, body) => body.FunctionsCalled() + inv.FunctionsCalled()
      case Check(e) => e.FunctionsCalled()
      case Assume(e) => e.FunctionsCalled()
      case Assign(_, rhs) => rhs.FunctionsCalled()
      case Call(proc, args) => SeqExprFunctionsCalled(proc.Pre) + SeqExprFunctionsCalled(proc.Post)
      case Escape(l) => {}
    }

    lemma VariablesDistinctBVars(vs: set<Variable>)
      requires VariablesDistinct(vs)
      ensures vs !! BVars()
    {
      match this
      case Seq(ss) => 
        DistinctSeqBVars(ss, vs) by {
          forall s | s in ss { s.VariablesDistinctBVars(vs); }
        }
      case _ => 
    }

    lemma VariablesDistinctUnion(vars1: set<Variable>, vars2: set<Variable>)
      requires VariablesDistinct(vars1)
      requires vars2 !! BVars()
      ensures VariablesDistinct(vars1 + vars2)
    {
      match this
      case Seq(ss) => SeqVariablesDistinctUnion(ss, vars1, vars2);
      case NewScope(vars, s) => 
        s.VariablesDistinctBVars(vars1 + vars);
        s.VariablesDistinctUnion(vars1 + vars, vars2);
        assert vars1 + vars + vars2 == vars1 + vars2 + vars;
      case _ => 
    }

//     predicate ImmutableVarsIdx(vars: set<Idx>, i: Idx) {
//       match this
//       case Assign(x, _) => x + i !in vars
//       case NewScope(n, s) => s.ImmutableVarsIdx(vars, i + n) 
//       case Seq(ss) => SeqImmutableVarsIdx(ss, vars, i)
//       case Choice(s0, s1) => s0.ImmutableVarsIdx(vars, i) && s1.ImmutableVarsIdx(vars, i)
//       case Loop(_, body) => body.ImmutableVarsIdx(vars, i)
//       case _ => true
//     }

//     predicate ImmutableVars(vars: set<Idx>) {
//       ImmutableVarsIdx(vars, 0)
//     }

    lemma IsDefinedOnTransitivity(d1: set<Variable>, d2: set<Variable>)
      requires d1 <= d2
      ensures IsDefinedOn(d1) ==> IsDefinedOn(d2)
    {  }

    ghost predicate IsSafe(m: M.Model) {
      match this
      case Check(e) => e.IsSafe(m)
      case Assume(e) => e.IsSafe(m)
      case Assign(_, e) => e.IsSafe(m)
      case Seq(ss) => SeqIsSafe(ss, m)
      case Choice(s0, s1) => s0.IsSafe(m) && s1.IsSafe(m)
      case NewScope(_, s) => s.IsSafe(m)
      case Escape(l) => true
      case Loop(inv, body) => inv.IsSafe(m) && body.IsSafe(m)
      case Call(proc, args) => true
    }
  }

  ghost predicate SeqIsSafe(ss: seq<Stmt>, m: M.Model) {
    forall s <- ss :: s.IsSafe(m)
  }

  lemma SeqIsSafeSeq(ss: seq<Stmt>, cont: seq<Stmt>, m: M.Model)
    requires SeqIsSafe([Seq(ss)] + cont, m)
    ensures SeqIsSafe(ss, m)
  {
    assert Seq(ss) in [Seq(ss)] + cont;
  }

  lemma ChoiceIsSafe(s1: Stmt, s2: Stmt, cont: seq<Stmt>, m: M.Model)
    requires SeqIsSafe([Choice(s1, s2)] + cont, m)
    ensures SeqIsSafe([s1] + cont, m)
    ensures SeqIsSafe([s2] + cont, m)
  {
    assert Choice(s1, s2) in [Choice(s1, s2)] + cont;
    assert Choice(s1, s2).IsSafe(m);
  }

  lemma NewScopeIsSafe(vars: set<Variable>, s: Stmt, cont: seq<Stmt>, m: M.Model)
    requires SeqIsSafe([NewScope(vars, s)] + cont, m)
    ensures SeqIsSafe([s], m)
  {
    assert NewScope(vars, s) in [NewScope(vars, s)] + cont;
    assert NewScope(vars, s).IsSafe(m);
  }

  lemma LoopIsSafe(inv: Expr, body: Stmt, cont: seq<Stmt>, m: M.Model)
    requires SeqIsSafe([Loop(inv, body)] + cont, m)
    ensures SeqIsSafe([Assume(inv), body, Check(inv), Assume(BConst(false))], m)
  {
    assert Loop(inv, body) in [Loop(inv, body)] + cont;
    assert Loop(inv, body).IsSafe(m);
  }

  ghost predicate SeqVariablesDistinct(ss: seq<Stmt>, vars: set<Variable>)
  {
    forall s <- ss :: s.VariablesDistinct(vars)
  }

  lemma SeqVariablesDistinctSeq(ss: seq<Stmt>, cont: seq<Stmt>, vars: set<Variable>)
    requires SeqVariablesDistinct([Seq(ss)] + cont, vars)
    ensures SeqVariablesDistinct(ss + cont, vars)
  {
    forall s | s in ss + cont ensures s.VariablesDistinct(vars) {
      if s in cont {
        assert s in [Seq(ss)] + cont;
      } else {
        assert Seq(ss) in [Seq(ss)] + cont;
        assert SeqVariablesDistinct(ss, vars);
      }
    }
  }

  lemma SeqVariablesDistinctChoice(s1: Stmt, s2: Stmt, cont: seq<Stmt>, vars: set<Variable>)
    requires SeqVariablesDistinct([Choice(s1, s2)] + cont, vars)
    ensures SeqVariablesDistinct([s1] + cont, vars)
    ensures SeqVariablesDistinct([s2] + cont, vars)
  {
    forall s | s in [s1] + [s2] + cont ensures s.VariablesDistinct(vars) {
      if s in cont {
        assert s in [Choice(s1, s2)] + cont;
      } else if s == s1 || s == s2 {
        assert Choice(s1, s2) in [Choice(s1, s2)] + cont;
        assert Choice(s1, s2).VariablesDistinct(vars);
      }
    }
  }



  lemma SeqVariablesDistinctNewScope(s: Stmt, vars: set<Variable>, cont: seq<Stmt>, vs: set<Variable>)
    requires SeqVariablesDistinct([NewScope(vars, s)] + cont, vs)
    ensures SeqVariablesDistinct([s], vs + vars)
    ensures vs + vars !! SeqBVars([s])
  {
    assert NewScope(vars, s) in [NewScope(vars, s)] + cont;
    assert NewScope(vars, s).VariablesDistinct(vs);
    s.VariablesDistinctBVars(vs + vars);
  }

  lemma SeqVariablesDistinctUnion(ss: seq<Stmt>, vars1: set<Variable>, vars2: set<Variable>)
    requires SeqVariablesDistinct(ss, vars1)
    requires vars2 !! SeqBVars(ss)
    ensures SeqVariablesDistinct(ss, vars1 + vars2)
  {
    forall s | s in ss ensures s.VariablesDistinct(vars1 + vars2) {
      DistinctSeqBVars'(ss, vars2, s);
      s.VariablesDistinctUnion(vars1, vars2);
    }
  }

  lemma SeqVariablesDistinctLoop(body: Stmt, inv: Expr, cont: seq<Stmt>, vars: set<Variable>)
    requires SeqVariablesDistinct([Loop(inv, body)] + cont, vars)
    ensures SeqVariablesDistinct([Assume(inv), body, Check(inv), Assume(BConst(false))], vars)
  {
    assert body.VariablesDistinct(vars) by {
      assert Loop(inv, body) in [Loop(inv, body)] + cont;
      assert Loop(inv, body).VariablesDistinct(vars);
    }
  }

  predicate SeqValidCalls(ss: seq<Stmt>) {
    forall s <- ss :: s.ValidCalls()
  }

  function SeqProceduresCalled(ss: seq<Stmt>): set<Procedure> {
    if ss == [] then {} else ss[0].ProceduresCalled() + SeqProceduresCalled(ss[1..])
  }

  function SeqFunctionsCalled(ss: seq<Stmt>): set<Function> {
    if ss == [] then {} else ss[0].FunctionsCalled() + SeqFunctionsCalled(ss[1..])
  }

  lemma SeqProceduresCalledLemma(ss: seq<Stmt>, s: Stmt, proc: Procedure)
    requires s in ss
    requires proc in s.ProceduresCalled()
    ensures proc in SeqProceduresCalled(ss)
  {

  }

//   predicate SeqImmutableVarsIdx(ss: seq<Stmt>, vars: set<Idx>, i: Idx)
//   {
//     if ss == [] then true else
//     ss[0].ImmutableVarsIdx(vars, i) && SeqImmutableVarsIdx(ss[1..], vars, i)
//   }

  function SeqSize(ss: seq<Stmt>): nat {
    if ss == [] then 0 else ss[0].Size() + SeqSize(ss[1..])
  }

  lemma SeqSizeSplitLemma(ss: seq<Stmt>)
    requires ss != []
    ensures SeqSize(ss) == ss[0].Size() + SeqSize(ss[1..])
  {  }

  function SeqFVars(ss: seq<Stmt>): set<Variable> 
  {
    if ss == [] then {} else ss[0].FVars() + SeqFVars(ss[1..])
  }

  function SeqBVars(ss: seq<Stmt>): set<Variable> {
    if ss == [] then {} else ss[0].BVars() + SeqBVars(ss[1..])
  }

  lemma DistinctSeqBVars(ss: seq<Stmt>, vars: set<Variable>)
    requires forall s <- ss :: vars !! s.BVars()
    ensures vars !! SeqBVars(ss)
  {  }

  lemma DistinctSeqBVars'(ss: seq<Stmt>, vars: set<Variable>, s: Stmt)
    requires vars !! SeqBVars(ss)
    requires s in ss
    ensures vars !! s.BVars()
  {  }

  predicate SeqIsDefinedOn(ss: seq<Stmt>, d: set<Variable>) 
    ensures SeqIsDefinedOn(ss, d) <==> SeqFVars(ss) <= d
  {
    if ss == [] then true else ss[0].IsDefinedOn(d) && SeqIsDefinedOn(ss[1..], d)
  }

  lemma SeqIsDefinedOnForall(ss: seq<Stmt>, d: set<Variable>)
    requires forall s <- ss :: s.IsDefinedOn(d)
    ensures SeqIsDefinedOn(ss, d)
  {
    // if ss != [] {
    //   assert ss[0].IsDefinedOn(d);
    //   assert SeqIsDefinedOn(ss[1..], d);
    // }
  }

  function SeqJumpDepth(ss: seq<Stmt>): nat {
    if ss == [] then 0 else max(ss[0].JumpDepth(), SeqJumpDepth(ss[1..]))
  }

  predicate SeqJumpsDefinedOn(ss: seq<Stmt>, d: nat) 
    ensures SeqJumpsDefinedOn(ss, d) <==> SeqJumpDepth(ss) <= d
  {
    if ss == [] then true else ss[0].JumpsDefinedOn(d) && SeqJumpsDefinedOn(ss[1..], d)
  }

  lemma SeqFunConcatLemmas(ss1: seq<Stmt>, ss2: seq<Stmt>)
    ensures SeqSize(ss1 + ss2) == SeqSize(ss1) + SeqSize(ss2)
    ensures SeqFVars(ss1 + ss2) == SeqFVars(ss1) + SeqFVars(ss2)
    ensures SeqBVars(ss1 + ss2) == SeqBVars(ss1) + SeqBVars(ss2)
    ensures SeqJumpDepth(ss1 + ss2) == max(SeqJumpDepth(ss1), SeqJumpDepth(ss2))
    ensures SeqFunctionsCalled(ss1 + ss2) == SeqFunctionsCalled(ss1) + SeqFunctionsCalled(ss2)
  {
    if ss1 == [] {
      assert ss1 + ss2 == ss2;
    } else {
      assert (ss1 + ss2)[0] == ss1[0];
      assert (ss1 + ss2)[1..] == ss1[1..] + ss2;
    }
  }

}