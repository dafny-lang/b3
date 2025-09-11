module Solvers {
  import opened Std.Wrappers
  import opened Basics
  import opened SolverExpr
  import Smt
  import opened DeclarationMarkers

  export
    reveals SolverState, ProofResult
    provides SolverState.Repr, SolverState.Valid
    provides SolverState.stack, SolverState.declarations
    reveals SolverState.IsTopMemo
    provides SolverState.Push, SolverState.Pop
    provides SolverState.DeclareType, SolverState.AddDeclarationMarker, SolverState.DeclareSymbol, SolverState.AddAssumption, SolverState.Prove
    provides Smt, Basics, SolverExpr, DeclarationMarkers

  datatype ProofResult =
    | Proved
    | Unproved(reason: string)
  
  /// This solver state can backtrack, however, it cannot spawn new SMT instances.
  /// The solver state includes a stack of (memo, marker set) pairs, which allows the solver
  /// to be shared (in a sequential fashion) among several clients. The clients then update
  /// the stack and marker set to keep track of what has been given to the underlying SMT solver.
  class SolverState<Memo(==)> {
    ghost const Repr: set<object>

    const smtEngine: Smt.SolverEngine
    var stack: List<(Memo, set<DeclarationMarker>)>

    var declarations: set<DeclarationMarker>

    constructor (smtEngine: Smt.SolverEngine)
      requires smtEngine.Valid() && smtEngine.CommandStacks() == Cons(Nil, Nil)
      ensures Valid() && fresh(Repr - {smtEngine, smtEngine.process})
    {
      this.smtEngine := smtEngine;
      this.stack := Nil;
      this.declarations := {};
      this.Repr := {this, smtEngine, smtEngine.process};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && smtEngine in Repr
      && smtEngine.process in Repr
      && this !in {smtEngine, smtEngine.process}
      && smtEngine.Valid()
      && stack.Length() + 1 == smtEngine.CommandStacks().Length()
    }

    predicate IsTopMemo(m: Memo)
      reads this
    {
      stack.Cons? && stack.head.0 == m
    }

    method Push(memo: Memo)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == Cons((memo, declarations), old(stack)) && declarations == old(declarations)
    {
      smtEngine.Push();
      stack := Cons((memo, declarations), stack);
    }

    method Pop()
      requires Valid() && stack.Cons?
      modifies Repr
      ensures Valid() && stack == old(stack).tail && declarations == old(stack).head.1
    {
      smtEngine.CommandStacks().AboutDoubleCons();
      smtEngine.Pop();
      var (_, decls) := stack.head;
      stack := stack.tail;
      declarations := decls;
    }

    method AddAssumption(expr: SExpr)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack) && declarations == old(declarations)
    {
      smtEngine.Assume(expr.ToString());
    }

    method DeclareType(decl: STypeDecl, marker: DeclarationMarker)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack) && declarations == old(declarations) + {marker}
    {
      smtEngine.DeclareSort(decl.name);
      declarations := declarations + {marker};
    }

    method AddDeclarationMarker(marker: DeclarationMarker)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack) && declarations == old(declarations) + {marker}
    {
      declarations := declarations + {marker};
    }

    method DeclareSymbol(decl: STypedDeclaration, marker: DeclarationMarker)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack) && declarations == old(declarations) + {marker}
    {
      DeclareSymbolByName(decl.name, SType.TypesToSExpr(decl.inputTypes), decl.typ.ToSExpr());
      declarations := declarations + {marker};
    }

    method DeclareSymbolByName(name: string, inputTpe: SExpr, outputTpe: SExpr)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack) && declarations == old(declarations)
    {
      smtEngine.DeclareFunction(name, inputTpe.ToString(), outputTpe.ToString());
    }

    method Prove(expr: SExpr) returns (result: ProofResult)
      requires Valid()
      modifies Repr
      ensures Valid() && stack == old(stack) && declarations == old(declarations)
    {
      smtEngine.Push();
      smtEngine.Assume(SExpr.Negation(expr).ToString());
      var satness := smtEngine.CheckSat();
      if satness == "unsat" {
        result := Proved;
      } else {
        var model := smtEngine.GetModel();
        result := Unproved(satness + "\n" + model);
      }
      smtEngine.Pop();
    }
  }
}
