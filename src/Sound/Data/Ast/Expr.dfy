module Expr {
  import opened Utils
  import opened State
  import M = Model
  import opened Std.Wrappers

  datatype Operator =
    // ternary operators
    | IfThenElse
    // binary operators
    | Equiv
    | LogicalImp
    | LogicalAnd | LogicalOr
    | Eql | Neql
    | Less | AtMost
    | Plus | Minus | Times | Div | Mod
    // unary operators
    | LogicalNot
    | UnaryMinus
  {
    function Type(): M.Type 
      requires !IfThenElse?
      requires !Eql?
      requires !Neql?
    {
      match this {
        case LogicalNot | Equiv | LogicalImp | LogicalAnd | LogicalOr => M.Bool
        case _ => M.Int
      }
    }

    function Arity() : nat {
      match this
      case IfThenElse => 3
      case LogicalNot | UnaryMinus => 1
      case _ => 2
    }

    function ToBinaryFunc(m: M.Model): (M.Any, M.Any) --> M.Any
      requires Arity() == 2
    {
      match this {
        case Equiv => m.Equiv
        case LogicalImp => m.Implies
        case LogicalAnd => m.LogicAnd
        case LogicalOr => m.Or
        case Eql => m.Eql
        case Neql => m.Neql
        case Less => m.Less
        case AtMost => m.AtMost
        case Plus => m.Plus
        case Minus => m.Minus
        case Times => m.Times
        case Div => m.Div
        case Mod => m.Mod
      }
    }

    function ToUnaryFunc(m: M.Model): M.Any --> M.Any
      requires Arity() == 1
    {
      match this {
        case LogicalNot => m.Not
        case UnaryMinus => m.Negate
      }
    }

    predicate CompatibleWith(args: seq<M.Any>, m: M.Model) {
      |args| == Arity() &&
      match this
      case IfThenElse => m.IsBool(args[0])
      case Eql | Neql => true 
      case _ => 
        if Type() == M.Int then
          && (forall i :: 0 <= i < |args| ==> m.IsInt(args[i]))
          && (Div? || Mod? ==> m.ToInt(args[1]) != 0)
        else if Type() == M.Bool then
          forall i :: 0 <= i < |args| ==> m.IsBool(args[i])
        else false
    }

    opaque function Eval(args: seq<M.Any>, m: M.Model): Option<M.Any>
    {
      if !CompatibleWith(args, m) then None
      else if Arity() == 3 then
        if m.IsBool(args[0]) then Some(args[0]) else Some(args[1])
      else if Arity() == 1 then
        Some(ToUnaryFunc(m)(args[0]))
      else if Arity() == 2 then
        Some(ToBinaryFunc(m)(args[0], args[1]))
      else None
    }

    greatest predicate RefEval(args: seq<M.Any>, outs: iset<M.Any>, m: M.Model)
    {
      Eval(args, m).Some? && Eval(args, m).value in outs
    }
  }

  lemma EqlEvalLemma(v1: M.Any, v2: M.Any, m: M.Model)
    ensures Eql.Eval([v1, v2], m) == Some(m.InterpBool(v1 == v2))
  {
    reveal Eql.Eval;
  }

  lemma AndEvalLemma(v1: M.Any, v2: M.Any, m: M.Model)
    requires m.IsBool(v1)
    requires m.IsBool(v2)
    ensures LogicalAnd.Eval([v1, v2], m) == Some(m.LogicAnd(v1, v2))
  {
    reveal LogicalAnd.Eval;
  }

  lemma ImpliesEvalLemma(v1: M.Any, v2: M.Any, m: M.Model)
    requires m.IsBool(v1)
    ensures LogicalImp.Eval([v1, v2], m) == 
      if m.IsBool(v2) then Some(m.Implies(v1, v2)) else None
  {
    reveal LogicalImp.Eval;
  }

  datatype Literal = Literal(value: string, typ: Type) {
    function ToLiteral(): M.Literal {
      M.Literal(value, typ.ToType())
    }
  }

  type FParameter = Variable

  datatype FunctionDefinition = FunctionDefinition(when: seq<Expr>, body: Expr)

  class Function {
    const Name: string
    const Parameters: seq<FParameter>
    const ResultType: Type
    var Definition: Option<FunctionDefinition>

    predicate HasBody() 
      reads this`Definition
    {
      Definition.Some?
    }

    function GetDef(): Expr
      requires HasBody()
      reads this`Definition
    {
      Definition.value.body
    }

    predicate ArgsCompatibleWith(args: seq<M.Any>, m: M.Model) {
      |args| == |Parameters| && forall i :: 0 <= i < |args| ==> m.HasType(args[i], Parameters[i].typ.ToType())
    }

    function ToFunction(): M.Function {
      M.Function(Name, seq(|Parameters|, (i: nat) requires i < |Parameters| => Parameters[i].typ.ToType()), ResultType.ToType())
    }

    predicate Valid()
      reads *
    {
      HasBody() ==> GetDef().IsDefinedOn(SetOfSeq(Parameters))
    }

    function FunctionsCalled(): set<Function>
      reads *
    {
      if HasBody() then GetDef().FunctionsCalled() else {}
    }

    function EvalArgs(args: seq<M.Any>, m: M.Model): Option<M.Any> {
      if ArgsCompatibleWith(args, m) then 
        Some(m.InterpFunctionOn(ToFunction(), args)) 
      else None
    }

    function ToState'(args: seq<M.Any>, params: seq<FParameter>): State 
      requires |args| == |params|
    {
      if params == [] then map[] else 
        map[params[0] := args[0]] + ToState'(args[1..], params[1..])
    }

    function ToState(args: seq<M.Any>): State 
      requires |args| == |Parameters|
    {
      ToState'(args, Parameters)
    }

    greatest predicate RefEval(args: seq<M.Any>, outs: iset<M.Any>, m: M.Model)
      reads *
    {
      && ArgsCompatibleWith(args, m)
      && var fval := m.InterpFunctionOn(ToFunction(), args);
        && fval in outs
        && (HasBody() ==> GetDef().RefEval(ToState(args), iset{fval}, m))
    }

    ghost predicate IsSound(m: M.Model)
      // requires Valid()
      reads *
    {
      HasBody() ==> 
        forall args: seq<M.Any> | ArgsCompatibleWith(args, m) :: 
          GetDef().RefEval(ToState(args), iset{m.InterpFunctionOn(ToFunction(), args)}, m)
    }

    lemma EvalSound(args: seq<M.Any>, funs: set<Function>, outs: iset<M.Any>, m: M.Model)
      requires EvalArgs(args, m).Some?
      requires forall func <- funs :: func.IsSound(m)
      requires forall func <- funs :: func.FunctionsCalled() <= funs
      requires this in funs
      requires EvalArgs(args, m).value in outs
      ensures RefEval(args, outs, m)
    {
      if HasBody() {
        assert ArgsCompatibleWith(args, m);
        // GetDef().EvalSound(ToState(args), funs);
        // calc {
        //   RefEval(args, iset{EvalArgs(args).value});
        //   == 
        //   GetDef().RefEval(ToState(args), iset{EvalArgs(args).value});
        // }
      }
    }
  }

  datatype Expr =
    | BConst(bvalue: bool)
    | IConst(ivalue: int)
    | CustomConst(value: Literal)
    | BVar(v: Variable)
    | OperatorExpr(op: Operator, args: seq<Expr>)
    | FunctionCallExpr(func: Function, args: seq<Expr>)
    | LetExpr(v: Variable, rhs: Expr, body: Expr)
    | QuantifierExpr(univ: bool, v: Variable, body: Expr) 
  {
    function FVars(): set<Variable>
    {
      match this
      case BConst(_) => {}
      case IConst(_) => {}
      case CustomConst(_) => {}
      case BVar(v) => {v}
      case OperatorExpr(op, args) => SeqExprFVars(args)
      case FunctionCallExpr(func, args) => SeqExprFVars(args)
      case LetExpr(v, rhs, body) => rhs.FVars() + (body.FVars() - {v})
      case QuantifierExpr(univ, v, body) => body.FVars() - {v}
    }

    predicate IsDefinedOn(vars: set<Variable>) 
    {
      FVars() <= vars
    }

    function FunctionsCalled(): set<Function>
    {
      match this
      case FunctionCallExpr(func, args) => {func} + SeqExprFunctionsCalled(args)
      case OperatorExpr(op, args) => SeqExprFunctionsCalled(args)
      case QuantifierExpr(univ, v, body) => body.FunctionsCalled()
      case LetExpr(v, rhs, body) => rhs.FunctionsCalled() + body.FunctionsCalled()
      case _ => {}
    }

    predicate ValidCalls()
      reads *
    {
      forall func <- FunctionsCalled() :: func.Valid()
    }

    ghost function Eval(s: State, m: M.Model): Option<M.Any>
      requires IsDefinedOn(s.Keys)
    {
      match this
      case BConst(bvalue)  => Some(m.InterpBool(bvalue))
      case IConst(ivalue)  => Some(m.InterpInt(ivalue))
      case BVar(id) => Some(s[id])
      case CustomConst(value) => Some(m.InterpLiteral(value.ToLiteral()))
      case OperatorExpr(op, args) => 
        var args :- SeqEval(args, s, m);
        op.Eval(args, m)
      case FunctionCallExpr(func, args) => 
        var args :- SeqEval(args, s, m);
        func.EvalArgs(args, m)
      case QuantifierExpr(true, v, body) =>
        if (forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            SomeBVal?(body.Eval(s.UpdateAt(v, x), m), m)) then 
          Some(m.InterpBool(forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            body.Eval(s.UpdateAt(v, x), m) == Some(m.True())
          ))
        else None
      case QuantifierExpr(false, v, body) =>
        if (forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            SomeBVal?(body.Eval(s.UpdateAt(v, x), m), m)) then 
          Some(m.InterpBool(exists x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            body.Eval(s.UpdateAt(v, x), m) == Some(m.True())
          ))
        else None
      case LetExpr(v, rhs, body) => 
        var x :- rhs.Eval(s, m);
        body.Eval(s.UpdateAt(v, x), m)
    }

    greatest predicate RefEval(s: State, outs: iset<M.Any>, m: M.Model)
      reads *
    {
      match this
      case BConst(bvalue) => m.InterpBool(bvalue) in outs
      case IConst(ivalue) => m.InterpInt(ivalue) in outs
      case CustomConst(value) => m.InterpLiteral(value.ToLiteral()) in outs
      case BVar(id) => v in s.Keys && s[id] in outs
      case OperatorExpr(op, args) => 
        exists outArgsSet: seq<iset<M.Any>> :: 
          && RefSeqEval(args, s, outArgsSet, m)
          && forall outArgs <- CrossProduct(outArgsSet) :: op.RefEval(outArgs, outs, m)
      case FunctionCallExpr(func, args) => 
        exists outArgsSet: seq<iset<M.Any>> :: 
          && RefSeqEval(args, s, outArgsSet, m)
          && forall outArgs <- CrossProduct(outArgsSet) :: func.RefEval(outArgs, outs, m)
      case LetExpr(v, rhs, body) => 
        exists outsRhs: iset<M.Any> :: 
          && rhs.RefEval(s, outsRhs, m)
          && forall out <- outsRhs :: body.RefEval(s.UpdateAt(v, out), outs, m)
      case QuantifierExpr(true, v, body) => 
        (forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            body.RefEval(s.UpdateAt(v, x), (iset v | m.IsBool(v)), m))
        &&
        ((m.True() in outs &&
          forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            body.RefEval(s.UpdateAt(v, x), iset{m.True()}, m))
        ||
        (m.False() in outs &&
          exists x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            body.RefEval(s.UpdateAt(v, x), iset{m.False()}, m)))
      case QuantifierExpr(false, v, body) =>
        (forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            body.RefEval(s.UpdateAt(v, x), (iset v | m.IsBool(v)), m))
        &&
        ((m.True() in outs &&
          exists x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            body.RefEval(s.UpdateAt(v, x), iset{m.True()}, m))
        ||
        (m.False() in outs &&
          forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
            body.RefEval(s.UpdateAt(v, x), iset{m.False()}, m)))
    }

    ghost predicate LetRefEval(s: State, u: Variable, rhs: Expr, body: Expr, outsRhs: iset<M.Any>, outs: iset<M.Any>, m: M.Model)
      reads *
    {
      forall out <- outsRhs :: body.RefEval(s.UpdateAt(u, out), outs, m)
    }

    lemma LetRefEvalUnfold(s: State, rhs: Expr, body: Expr, outs: iset<M.Any>, v: Variable, m: M.Model) returns (outsRhs: iset<M.Any>)
      requires LetExpr(v, rhs, body).RefEval(s, outs, m)
      ensures rhs.RefEval(s, outsRhs, m)
      ensures forall out <- outsRhs :: body.RefEval(s.UpdateAt(v, out), outs, m)
    {
      var outsRhs' :| rhs.RefEval(s, outsRhs', m) &&
        LetRefEval(s, v, rhs, body, outsRhs', outs, m);
      outsRhs := outsRhs';
      forall out | out in outsRhs ensures body.RefEval(s.UpdateAt(v, out), outs, m) {
        assert LetRefEval(s, v, rhs, body, outsRhs, outs, m) ==> forall out <- outsRhs :: body.RefEval(s.UpdateAt(v, out), outs, m);
      }
    }

    lemma EvalComplete(s: State, outs: iset<M.Any>, m: M.Model)
      requires RefEval(s, outs, m)
      // ensures outs != iset{}
      ensures IsDefinedOn(s.Keys)
      ensures Eval(s, m).Some? 
      ensures Eval(s, m).value in outs
    {
      match this
      case OperatorExpr(op, args) => 
        var outArgsSet :| 
          && RefSeqEval(args, s, outArgsSet, m)
          && (forall outArgs <- CrossProduct(outArgsSet) :: op.RefEval(outArgs, outs, m));
        SeqEvalComplete(args, s, outArgsSet, m);
      case FunctionCallExpr(func, args) => 
        var outArgsSet :| 
          && RefSeqEval(args, s, outArgsSet, m)
          && (forall outArgs <- CrossProduct(outArgsSet) :: func.RefEval(outArgs, outs, m));
        SeqEvalComplete(args, s, outArgsSet, m);
      case LetExpr(v, rhs, body) => 
        var outsRhs := LetRefEvalUnfold(s, rhs, body, outs, v, m);
        rhs.EvalComplete(s, outsRhs, m);
      case QuantifierExpr(true, v, body) => 
        var x := m.NoEmptyTypes(v.typ.ToType());
        if (forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
          body.RefEval(s.UpdateAt(v, x), iset{m.True()}, m)) {
        }
      case QuantifierExpr(false, v, body) => 
        var x := m.NoEmptyTypes(v.typ.ToType());
        if (exists x: M.Any | m.HasType(x, v.typ.ToType()) :: 
          body.RefEval(s.UpdateAt(v, x), iset{m.True()}, m)) {
        }
      case _ => 
    }

    lemma EvalSound(s: State, funs: set<Function>, outs: iset<M.Any>, m: M.Model)
      requires FunctionsCalled() <= funs
      requires forall func <- funs :: func.IsSound(m)
      requires forall func <- funs :: func.FunctionsCalled() <= funs
      requires IsDefinedOn(s.Keys)
      requires Eval(s, m).Some?
      requires Eval(s, m).value in outs
      ensures RefEval(s, outs, m)
    {
      match this
      case OperatorExpr(op, args) => 
        SeqEvalSound(args, s, funs, SeqSingleton(SeqEval(args, s, m).value), m);
        CrossProductSeqSingleton(SeqEval(args, s, m).value);
      case FunctionCallExpr(func, args) => 
        SeqEvalSound(args, s, funs, SeqSingleton(SeqEval(args, s, m).value), m);
        CrossProductSeqSingleton(SeqEval(args, s, m).value);
        func.EvalSound(SeqEval(args, s, m).value, funs, outs, m );
      case LetExpr(v, rhs, body) => rhs.EvalSound(s, funs, iset{rhs.Eval(s, m).value}, m);
      case QuantifierExpr(true, v, body) => 
        assert forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
          SomeBVal?(body.Eval(s.UpdateAt(v, x), m), m);
        if !(forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
          body.Eval(s.UpdateAt(v, x), m) == Some(m.True())) {
          var x: M.Any :| m.HasType(x, v.typ.ToType()) &&
            body.Eval(s.UpdateAt(v, x), m) != Some(m.True());
          m.BoolIsTrueOrFalse(body.Eval(s.UpdateAt(v, x), m).value);
        }
      case QuantifierExpr(false, v, body) => 
        assert forall x: M.Any | m.HasType(x, v.typ.ToType()) :: 
          SomeBVal?(body.Eval(s.UpdateAt(v, x), m), m);
        if !(exists x: M.Any | m.HasType(x, v.typ.ToType()) :: 
          body.Eval(s.UpdateAt(v, x), m) == Some(m.True())) {
          forall x: M.Any | m.HasType(x, v.typ.ToType()) {
            m.BoolIsTrueOrFalse(body.Eval(s.UpdateAt(v, x), m).value);
          }
        }
      case _ =>
    }

    ghost predicate HoldsOn(s: State, m: M.Model) 
      requires IsDefinedOn(s.Keys)
    {
      Eval(s, m) == Some(m.True())
    }

    ghost predicate Holds(md: M.Model) {
      forall s: State :: IsDefinedOn(s.Keys) ==> HoldsOn(s, md)
    }


    ghost predicate RefHoldsOn(s: State, m: M.Model)
      reads *
    {
      RefEval(s, iset{m.True()}, m)
    }

    lemma HoldsOnSound(s: State, funs: set<Function>, m: M.Model)
      requires FunctionsCalled() <= funs
      requires forall func <- funs :: func.IsSound(m)
      requires forall func <- funs :: func.FunctionsCalled() <= funs
      ensures (IsDefinedOn(s.Keys) && HoldsOn(s, m)) == RefHoldsOn(s, m)
    {
      if IsDefinedOn(s.Keys) && HoldsOn(s, m) {
        EvalSound(s, funs, iset{m.True()}, m);
      }
      if RefHoldsOn(s, m) {
        EvalComplete(s, iset{m.True()}, m);
      }
    }

    lemma EvalFVarsLemma(s1: State, s2: State, m: M.Model) 
      requires IsDefinedOn(s1.Keys)
      requires IsDefinedOn(s2.Keys)
      requires forall v: Variable :: v in FVars() ==> s1[v] == s2[v]
      ensures Eval(s1, m) == Eval(s2, m)
    { 
      match this
      case QuantifierExpr(true, v, body) => 
      case QuantifierExpr(false, v, body) => 
      case FunctionCallExpr(func, args) => SeqEvalFVarsLemma(args, s1, s2, m);
      case OperatorExpr(op, args) => SeqEvalFVarsLemma(args, s1, s2, m);
      case _ => 
    } 

    ghost predicate RefHolds(md: M.Model)
      reads *
    {
      forall s: State :: IsDefinedOn(s.Keys) ==> RefHoldsOn(s, md)
    }

    ghost function Sem(m: M.Model): iset<State> 
    { 
      iset st: State | IsDefinedOn(st.Keys) && HoldsOn(st, m) 
    }

    ghost predicate IsSafe(m: M.Model) {
      forall s: State | IsDefinedOn(s.Keys) :: Eval(s, m).Some?
    }
  }

  ghost predicate SeqHolds(ss: seq<Expr>, md: M.Model)
  {
    forall e <- ss :: e.Holds(md)
  }

  ghost predicate SeqRefHolds(ss: seq<Expr>, md: M.Model)
    reads *
  {
    forall e <- ss :: e.RefHolds(md)
  }

  ghost predicate SeqRefHoldsWith(ss: seq<Expr>, funs: set<Function>)
    reads *
  {
    forall md: M.Model ::
      (forall func <- funs :: func.IsSound(md)) ==> SeqRefHolds(ss, md)
  }

  function SeqExprFunctionsCalled(ss: seq<Expr>): set<Function>
  {
    if ss == [] then {} else ss[0].FunctionsCalled() + SeqExprFunctionsCalled(ss[1..])
  }

  lemma SeqExprFunctionsCalledIn(ss: seq<Expr>, s: Expr)
    requires s in ss
    ensures s.FunctionsCalled() <= SeqExprFunctionsCalled(ss)
  {
  }

  ghost function CrossProduct<T(!new)>(ss: seq<iset<T>>): iset<seq<T>> {
    iset s | 
      && |s| == |ss|
      && forall i: nat | i < |ss| :: s[i] in ss[i]
  }

  function SeqSingleton(s: seq): seq<iset> {
    seq(|s|, (i: nat) requires i < |s| => iset{s[i]})
  }

  lemma SeqSingletonCons<T>(s: T, ss: seq)
    ensures SeqSingleton([s] + ss) == [iset{s}] + SeqSingleton(ss)
  { }

  lemma CrossProductSeqSingleton<T(!new)>(ss: seq)
    ensures CrossProduct(SeqSingleton(ss)) == iset{ss}
  {
    forall s <- CrossProduct(SeqSingleton(ss)) ensures s == ss { }
  }

  greatest predicate RefSeqEval(ss: seq<Expr>, s: State, outSeqs: seq<iset<M.Any>>, m: M.Model) 
    reads *
  {
    if ss == [] then outSeqs == [] else
    && |outSeqs| > 0
    && ss[0].RefEval(s, outSeqs[0], m)
    && RefSeqEval(ss[1..], s, outSeqs[1..], m)
  }

  ghost function SeqEval(ss: seq<Expr>, s: State, m: M.Model): Option<seq<M.Any>>
    requires SeqExprFVars(ss) <= s.Keys
    ensures SeqEval(ss, s, m).Some? ==> |SeqEval(ss, s, m).value| == |ss|
  {
    if ss == [] then Some([]) else
    var e :- ss[0].Eval(s, m);
    var es :- SeqEval(ss[1..], s, m);
    Some([e] + es)
  }

  lemma SeqEvalComplete(ss: seq<Expr>, s: State, outs: seq<iset<M.Any>>, m: M.Model)
    requires RefSeqEval(ss, s, outs, m)
    ensures SeqExprFVars(ss) <= s.Keys
    ensures SeqEval(ss, s, m).Some?
    ensures SeqEval(ss, s, m).value in CrossProduct(outs)
  {
    if ss != [] {
      ss[0].EvalComplete(s, outs[0], m);
      SeqEvalComplete(ss[1..], s, outs[1..], m);
      var o :| o in outs[0];
      var os :| os in CrossProduct(outs[1..]);
      assert [o] + os in CrossProduct(outs);
    } else {
      assert [] in CrossProduct(outs);
    }
  }

  lemma SeqEvalSound(ss: seq<Expr>, s: State, funs: set<Function>, outs: seq<iset<M.Any>>, m: M.Model)
    requires SeqExprFVars(ss) <= s.Keys
    requires forall func <- funs :: func.IsSound(m)
    requires forall func <- funs :: func.FunctionsCalled() <= funs
    requires SeqEval(ss, s, m).Some?
    requires SeqExprFunctionsCalled(ss) <= funs
    requires SeqEval(ss, s, m).value in CrossProduct(outs)
    ensures RefSeqEval(ss, s, outs, m)
  {
    if ss != [] {
      ss[0].EvalSound(s, funs, outs[0], m);
      SeqEvalSound(ss[1..], s, funs, outs[1..], m);
      SeqSingletonCons(ss[0].Eval(s, m).value, SeqEval(ss[1..], s, m).value);
    }
  }

  lemma SeqEval1(e: Expr, s: State, m: M.Model)
    requires e.IsDefinedOn(s.Keys)
    requires e.Eval(s, m).Some?
    ensures SeqEval([e], s, m) == Some([e.Eval(s, m).value])
  {
    calc {
      SeqEval([e], s, m);
      == { assert [e][1..] == [];
           assert [e][0] == e; }
      Some([e.Eval(s, m).value] + []);
      == { assert [e.Eval(s, m).value] + [] == [e.Eval(s, m).value]; }
      Some([e.Eval(s, m).value]);
    }
  }

  lemma SeqEval2(e1: Expr, e2: Expr, s: State, m: M.Model)
    requires e1.IsDefinedOn(s.Keys)
    requires e2.IsDefinedOn(s.Keys)
    requires e1.Eval(s, m).Some?
    requires e2.Eval(s, m).Some?
    ensures SeqExprFVars([e1, e2]) <= s.Keys
    ensures SeqEval([e1, e2], s, m) == Some([e1.Eval(s, m).value, e2.Eval(s, m).value])
  {
    assert [e1, e2][1..] == [e2];
    assert [e1, e2][0] == e1;
    SeqFVarsPairLemma(e1, e2);
    SeqEval1(e2, s, m); 
    calc {
      SeqEval([e1, e2], s, m);
      == { assert [e1, e2][1..] == [e2];
            assert [e1, e2][0] == e1;
            SeqEval1(e2, s, m); }
      Some([e1.Eval(s, m).value] + SeqEval([e2], s, m).value);
      == { SeqEval1(e2, s, m);
            assert [e1.Eval(s, m).value] + [e2.Eval(s, m).value] == [e1.Eval(s, m).value, e2.Eval(s, m).value]; }
      Some([e1.Eval(s, m).value, e2.Eval(s, m).value]);
    }
  }

  lemma SeqEvalFVarsLemma(ss: seq<Expr>, s1: State, s2: State, m: M.Model)
    requires SeqExprFVars(ss) <= s1.Keys
    requires SeqExprFVars(ss) <= s2.Keys
    requires forall v: Variable :: v in SeqExprFVars(ss) ==> s1[v] == s2[v]
    ensures SeqEval(ss, s1, m) == SeqEval(ss, s2, m)
  {
    if ss != [] {
      ss[0].EvalFVarsLemma(s1, s2, m);
      SeqEvalFVarsLemma(ss[1..], s1, s2, m);
    }
  }
  
  function SeqExprFVars(ss: seq<Expr>): set<Variable>
  {
    if ss == [] then {} else ss[0].FVars() + SeqExprFVars(ss[1..])
  }

  function And(e0: Expr, e1: Expr): Expr {
    OperatorExpr(LogicalAnd, [e0, e1])
  }

  function Implies(e0: Expr, e1: Expr): Expr {
    OperatorExpr(LogicalImp, [e0, e1])
  }

  function Eq(e1: Expr, e2: Expr): Expr {
    OperatorExpr(Eql, [e1, e2])
  }

  lemma SeqFVarsPairLemma(e1: Expr, e2: Expr)
    ensures SeqExprFVars([e1, e2]) == e1.FVars() + e2.FVars()
  {
    calc {
      SeqExprFVars([e1, e2]);
      ==
      e1.FVars() + SeqExprFVars([e2]);
      ==
      e1.FVars() + e2.FVars() + {};
    }
  }

  lemma EvalEqLemma(e1: Expr, e2: Expr, s: State, m: M.Model)
    requires e1.IsDefinedOn(s.Keys)
    requires e2.IsDefinedOn(s.Keys)
    requires e1.Eval(s, m) == e2.Eval(s, m)
    requires e1.Eval(s, m).Some?
    ensures Eq(e1, e2).IsDefinedOn(s.Keys)
    ensures Eq(e1, e2).IsDefinedOn(s.Keys)
    ensures Eq(e1, e2).HoldsOn(s, m)
  { 
    SeqFVarsPairLemma(e1, e2);
    calc {
      Eq(e1, e2).Eval(s, m);
      ==
      OperatorExpr(Eql, [e1, e2]).Eval(s, m);
      == { SeqEval2(e1, e2, s, m); }
      Eql.Eval([e1.Eval(s, m).value, e2.Eval(s, m).value], m);
      == { EqlEvalLemma(e1.Eval(s, m).value, e2.Eval(s, m).value, m); }
      Some(m.InterpBool(e1.Eval(s, m).value == e2.Eval(s, m).value));
      == { assert e1.Eval(s, m) == e2.Eval(s, m); }
      Some(m.InterpBool(true));
    }
  }

  lemma SeqExprFVarsLemma(ss: seq<Expr>, s: Expr) 
    requires s in ss
    ensures s.FVars() <= SeqExprFVars(ss)
  {  }

  lemma SeqExprFVarsLemma'(ss: seq<Expr>, d: set<Variable>) 
    requires forall e <- ss :: e.FVars() <= d
    ensures SeqExprFVars(ss) <= d
  {
    if ss != [] {
      assert SeqExprFVars(ss) == ss[0].FVars() + SeqExprFVars(ss[1..]);
      assert ss[0].FVars() <= d;
      assert SeqExprFVars(ss[1..]) <= d;
    }
  }

  lemma IsDefinedOnAndLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(s.Keys) 
    requires e1.IsDefinedOn(s.Keys)
    ensures And(e0, e1).IsDefinedOn(s.Keys) 
  { 
    SeqFVarsPairLemma(e0, e1);
  }

  lemma HoldsOnAndLemma(e0: Expr, e1: Expr, s: State, m: M.Model)
    requires e0.IsDefinedOn(s.Keys)
    requires e1.IsDefinedOn(s.Keys)
    requires e0.HoldsOn(s, m)
    requires e1.HoldsOn(s, m)
    ensures And(e0, e1).IsDefinedOn(s.Keys) 
    ensures And(e0, e1).HoldsOn(s, m)
  {
    SeqFVarsPairLemma(e0, e1);
    SeqEval2(e0, e1, s, m);
    AndEvalLemma(e0.Eval(s, m).value, e1.Eval(s, m).value, m);
  }

  lemma HoldsOnImpliesLemma(e0: Expr, e1: Expr, s: State, m: M.Model)
    requires e0.IsDefinedOn(s.Keys)
    requires e1.IsDefinedOn(s.Keys)
    requires e0.HoldsOn(s, m)
    requires (
      IsDefinedOnImpliesLemma(e0, e1, s);
      Implies(e0, e1).HoldsOn(s, m))
    ensures e1.HoldsOn(s, m)
  {
    IsDefinedOnImpliesLemma(e0, e1, s);
    assert e0.Eval(s, m).Some?;
    assert SeqEval([e0, e1], s, m).Some?;
    if e1.Eval(s, m).Some? {
      SeqEval2(e0, e1, s, m);
      calc {
        Implies(e0, e1).Eval(s, m).value;
        == { SeqEval2(e0, e1, s, m);
             ImpliesEvalLemma(e0.Eval(s, m).value, e1.Eval(s, m).value, m); }
        m.Implies(e0.Eval(s, m).value, e1.Eval(s, m).value);
        ==
        m.Implies(m.True(), e1.Eval(s, m).value);
        == { }
        m.InterpBool(true ==> m.ToBool(e1.Eval(s, m).value));
        == { }
        m.InterpBool(m.ToBool(e1.Eval(s, m).value));
      }
    }
  }

  lemma IsDefinedOnImpliesLemma(e0: Expr, e1: Expr, s: State)
    requires e0.IsDefinedOn(s.Keys)
    requires e1.IsDefinedOn(s.Keys)
    ensures Implies(e0, e1).IsDefinedOn(s.Keys)
  { 
    SeqFVarsPairLemma(e0, e1);
  }

  function Conj(ctx: seq<Expr>): Expr 
  {
    if ctx == [] then BConst(true) else And(ctx[0], Conj(ctx[1..]))
  }

  lemma FVarsConjUnionLemma(ctx1: seq<Expr>, ctx2: seq<Expr>)
    ensures Conj(ctx1 + ctx2).FVars() == Conj(ctx1).FVars() + Conj(ctx2).FVars()
  {
    if ctx1 == [] {
      assert [] + ctx2 == ctx2;
    } else {
      assert ctx1 + ctx2 == [ctx1[0]] + (ctx1[1..] + ctx2);
      calc {
        Conj(ctx1 + ctx2).FVars();
        ==
        And(ctx1[0], Conj(ctx1[1..] + ctx2)).FVars();
        == { SeqFVarsPairLemma(ctx1[0], Conj(ctx1[1..] + ctx2)); }
        ctx1[0].FVars() + Conj(ctx1[1..] + ctx2).FVars();
        == { SeqFVarsPairLemma(ctx1[0], Conj(ctx1[1..])); }
        Conj(ctx1).FVars() + Conj(ctx2).FVars();
      }
    }
  }

  lemma EvalConjLemma(ctx: seq<Expr>, s: State, m: M.Model)
    requires forall e <- ctx :: e.IsDefinedOn(s.Keys)
    requires forall e <- ctx :: e.HoldsOn(s, m)
    ensures Conj(ctx).IsDefinedOn(s.Keys)
    ensures Conj(ctx).HoldsOn(s, m)
  {  
    if ctx != [] { 
      IsDefinedOnAndLemma(ctx[0], Conj(ctx[1..]), s); 
      HoldsOnAndLemma(ctx[0], Conj(ctx[1..]), s, m);
    }  
  }

}