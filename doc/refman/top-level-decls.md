# Top-level declarations

A _program_ consists of a list of top-level declarations. The order of these is irrelevant.

```
Program ::=
  | TypeDecl
  | Tagger
  | Function
  | Axiom
  | Procedure
```

## Types

```
TypeDecl ::=
  type Identifier
```

This declares a nonempty but otherwise uninterpreted type.

There are two built-in types, so the use of type is

```
Type ::=
  | bool
  | int
  | Identifier
```

## Taggers

```
Tagger ::=
  tagger Identifier for Type
```

## Functions

```
Function ::= 
  function Identifier "(" FParameter*, ")" ":" Type [ "tag" Identifier ]
  [
    ( "when" Expression )*
    "{" Expression "}"
  ]

FParameter ::=
  [ "injective" ] Identifier ":" Type
```

## Axioms

```
Axiom ::=
  axiom [ explains Identifier+, ]
    Expression
```

## Procedures

```
Procedure ::=
  procedure Identifier "(" PParameter*, ")"
    Spec*
  [ BlockStmt ]

FParameter ::=
  [ "inout" | "out" ] Identifier ":" Type

Spec ::=
  | requires AExpression
  | ensures AExpression

AExpression ::=
  | Expression
  | BlockStmt
```

There are restrictions on the `BlockStmt` version of `AExpression` as to which statements the block
is allowed to contain.

There are three parameter modes: in, inout, and out. The absence of `inout` and `out` indicates an
in-argument.

In the procedure body, in-parameters are immutable and inout- and out-parameters are mutable.