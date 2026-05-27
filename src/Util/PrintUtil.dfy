module PrintUtil {
  export
    provides Indent, IndentAmount
    provides CustomLiteralToString
    reveals ExprFormatOption, BindingPower, Side, TieBreaker
    provides ExprFormatOption.Space, ExprFormatOption.More
    provides BindingPower.Init, BindingPower.EndlessOperator, BindingPower.SubexpressionPower
    provides Parenthesis, ParenthesisWrap

  method Indent(indent: nat, s: string := "") {
    for i := 0 to indent {
      print " ";
    }
    print s;
  }

  const IndentAmount: nat := 2

  datatype ExprFormatOption = SingleLine | MultipleLines(indent: nat)
  {
    method Space() {
      match this
      case SingleLine => print " ";
      case MultipleLines(indent) =>
        print "\n";
        Indent(indent);
    }

    function More(): ExprFormatOption {
      match this
      case SingleLine => this
      case MultipleLines(indent) =>
        MultipleLines(indent + IndentAmount)
    }
  }

  function CustomLiteralToString(s: string, typeName: string): string {
    "|" + s + ": " + typeName + "|"
  }

  // An operator (or keyword) appearing in an expression has a kind of "magnetism" on
  // both sides. The magnetism says how much of a force the operator exerts to the left
  // (on its leftmost subexpression) and to the right (on its rightmost subexpression).
  //
  //       expr    <--left force---  OPERATOR  ---right force-->    expr
  //
  // The context where the expression appears also exerts some force on both sides.
  //
  //       ---context force from left-->  expr  <--context force from right---
  //
  // If an operator exerts more force on its leftmost and rightmost arguments than
  // the surrounding context, then it "wins" and no parentheses are needed when printing
  // the expression in that context.
  //
  // 0 is the lowest force. It says that no claim is made on the expression in that direction.
  //
  // A left-associative operator has a slightly larger pull on its right argument.
  // A right-associative operator has a slightly larger pull on its left argument.
  //
  // When the context and operator exert the same force on a subexpression, there are different
  // ways of breaking the tie:
  //     - operator wins
  //     - context wins
  //     - operator wins if both operator and context are of the same "family"
  datatype BindingPower = BindingPower(left: nat, right: nat, tieBreaker: TieBreaker := OperatorWins)
  {
    static const Init := BindingPower(0, 0)
    static const EndlessOperator := BindingPower(1000, 0)

    predicate WinsOver(context: BindingPower) {
      if tieBreaker.BreakTieInFavorOfOperator(context.tieBreaker) then
        context.left <= left && context.right <= right
      else
        context.left < left && context.right < right
    }

    function SubexpressionPower(side: Side, context: BindingPower): BindingPower {
      // adjust the context for parentheses that would have been added
      var adjustedContext := if WinsOver(context) then context else Init;
      match side
      case Left => BindingPower(adjustedContext.left, left, tieBreaker)
      case Right => BindingPower(right, adjustedContext.right, tieBreaker)
    }
  }

  datatype Side = Left | Right

  datatype TieBreaker = OperatorWins | ContextWins | SameFamilyWins(n: nat)
  {
    predicate BreakTieInFavorOfOperator(context: TieBreaker) {
      || this == OperatorWins
      || context == OperatorWins
      || (this.SameFamilyWins? && this == context)
    }
  }

  method Parenthesis(side: Side, opStrength: BindingPower, context: BindingPower) {
    if !opStrength.WinsOver(context) {
      match side
      case Left => print "(";
      case Right => print ")";
    }
  }

  function ParenthesisWrap(opStrength: BindingPower, contextStrength: BindingPower, s: string): string {
    if opStrength.WinsOver(contextStrength) then
      s
    else
      "(" + s + ")"
  }
}