# array-lang

A programming language built around arrays with shapes encoded in types.
All done in Lean with the intention of proving some correctness properties about types of the language.
Almost all written without AI, with exceptions of generating test cases and Lean macros to make prettier syntax.

In its current state, a toy example of a type inference algorithm for such a language (a modified form of Hindley-Milner). Also includes a Lean implementation of original Hindley-Milner.

The basic idea is that every object is an n-dimensional array with a shape described by an n-tuple, and functions can be dependently typed (output shape depends on input shape). This is already very natural when working with matrices: the shape of A \* B (where \* denotes matrix multiplication) depends on the shape of A and B, and you can only compute A \* B given a constraint on the shapes of A and B (namely, B must have the same number of rows as A has columns).

Given this, a great motivating example is something like A \* B \* C where we know A : (2, 3) and C : (4, 5), but B has unknown shape. A good type inference algorithm should infer that B : (3, 4) and that A \* B \* C : (2, 5). And this shape inference should work in context of other language features like branching, anonymous functions, let-in polymorphism, etc.

Our toy array language does exactly this for 2D matrices containing only integer elements, without branching. Even with just this, we can do some cool things like defining an identity matrix which is polymorphic over all sizes and + and \* operations which enforce shapes:

```
-- initial environment with types of built-ins
abbrev initialEnv := Env.ofList [
  ("*", [sch| forall #0 #1 #2, (#0, #1) -> (#1, #2) -> (#0, #2)]),
  ("+", [sch| forall #0 #1, (#0, #1) -> (#0, #1) -> (#0, #1)]),
  ("I", [sch| forall #0, (#0, #0)])
]
```

And this lets us test the example above:

```
def test_env := Env.extendInitial <| Env.ofList [
    ("A", [ty| (2, 3)]),
    ("C", [ty| (4, 5)]),
]
#eval infer [lang| fun B => A * B * C] test_env -- Except.ok (3, 4) -> (2, 5)
```

TODO:

Short term

- carrier types
- broadcasting
-

Long term

- parser of actual text file
- semantics
- some kind of proof of correctness
