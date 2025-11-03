
TODO: 
  - write up explanations of
    - sigantures
    - algebras
    - displayed algebras
  - code up 
    - RLE signature example
    - RLE algebra examples (including the trivial algebra)
    - RLE as List displayed algebra
    - coherency
    - inductive algebra definition
    - representations
    - computation irrelevance of representations


```idris
module CustomReprInductiveFamilies
import Data.Vect
%default total
```

The goal of the paper (and hence this implementation) is to provide a way to have more performant run-time representations of complicated inductive families by proving that the user-given run-time representation behaves exactly like the inductive family.

We're using Idris2's native type system as our type theory as well as the metatheory. However, in order to describe a depdendent data type, we need some way of referencing its inputs. For example, take the Run-Length Encoding of a list from chapter 3.2.2 of the paper Idris 2: Quantitative Type Theory in Practice by Edwin Brady:

```idris
repeat : Nat -> a -> List a
repeat Z x = []
repeat (S n) x = x :: repeat n x

data RLE : {0ty : Type} -> (List ty) -> Type where
  Empty : {0ty : Type} -> RLE {ty = ty} []
  Run : {0ty : Type} -> {0ys : List ty} -> 
        (n : Nat) -> (x : ty) -> (rle : RLE ys) -> RLE (repeat (S n) x ++ ys)
```

For clarity, all the implicit arguments to the data type and the constructors are given.

In order to generalise this, we need a way to talk about the (implicit and explicit) "inputs" to the `RLE` type - a dependent pair of a `ty : Type` and a `List ty`. We could use Idris2's dependent pair construct for this:

<!-- idris
depPairToRLE : (ty : Type ** List ty) -> Type
depPairToRLE (ty ** xs) = RLE {ty = ty} xs
-->

But we want to be able to talk about any given inductively defined family of data types. How do we abstract this to talk about _any_ such dependent pair? Or a finitely long nested sequence of dependent pairs? Idris2 doesn't give us an abstraction over any dependent pair, so this part of the theory we'll have to construct ourselves.

A finitely long nested sequence of dependent pairs is called a telescope. For example, `(ty : Type ** List ty)` is a telescope. In general, a telescope is a dependent sequence of the form `(x0 : T0 ** x1 : T1(x0) ** x2 : T2(x0, x1) ** ... xn : Tn(x0, ..., x{n-1}))`.

Below we've defined `Tel` as a nested sequence of types, which can possibly depend on previous types in the sequence:

```idris
data Tel : Type where
  Dot : Tel
  (.*.) : (A : Type) -> (a : A -> Tel) -> Tel

export infixr 10 .*.
```

So our RLE inputs would be represented as the telescope

```idris
RLETel : Tel
RLETel = Type .*. (\ty => List ty .*. (\l => Dot))
```

But how do we get an actual instance of this telescope? For example, in Idris2 the terms for a dependent pair are overloaded with the type construction `**`, so we could have the following be valid

<!-- idris
rleDepPairExample : (ty : Type ** List ty)
rleDepPairExample = (Int ** [1])
-->

An instance of a telescope is called a spine. We can define our a spine of a particular telescope as following:

```idris
data Spine : (T : Tel) -> Type where
  SEmpty : Spine Dot
  (.+.) : {0A : Type} -> {0T : A -> Tel} ->  (a : A) -> Spine (T a) -> Spine (A .*. T)

export infixr 10 .+.
```

We've chosen not to overload the telescope and spine constructor for clarity.

Below are a couple of helper functions for constructing telescopes and spines from the right instead of the left - useful for when you have a telescope and want to insert another type depending on all the previous ones.

- Insert `X` on the right of the telescope, (possibly) depending on previous telescope values:

```idris
(.**.) : (T : Tel) -> (X : Spine T -> Type) -> Tel
(.**.) Dot x = x SEmpty .*. (\x => Dot)
(.**.) (a .*. lam) x = a .*. (\a => 
                       let
                          x' : Spine (lam a) -> Type
                          x' s = x (a .+. s)
                       in
                       (.**.) (lam a) x')

export infixl 10 .**.
```

- Insert `x` on the right of the spine, where the type of x (possibly) depends on previous spine values:

```idris
(.++.) : {T : Tel} -> {X : Spine T -> Type} -> (delta : Spine T) -> (x : X delta) -> Spine (T .**. X)
(.++.) SEmpty x = x .+. SEmpty
(.++.) (a .+. s) x = a .+. ((.++.) s x)

export infixl 10 .++.
```

- Given a(n implicit) family `B`, a function `f` to construct a `B`, and a term `a` for the first element of `B`'s inputs, return a function `f` to construct a `B` with the first input as `a`:

```idris
app : {0A : Type} -> {0T : A -> Tel} -> {0B : Spine (A .*. T) -> Type} -> 
     (f : (v : Spine (A .*. T)) -> B v) -> (a : A) -> (v' : Spine (T a)) -> B (a .+. v')
app f a v' = f (a .+. v')
```

```idris
data OpTerm : (T : Tel) -> Type where
  IotaTerm : {T : Tel} -> Spine T -> OpTerm T

data Op : (T : Tel) -> Type where
  Iota' : {T : Tel} -> OpTerm T -> Op T
  IntArr : {T : Tel} -> OpTerm T -> Op T -> Op T
  ExtArr' : {T : Tel} -> (A : Type) -> ((a : A) -> Op T) -> Op T

Iota : {T : Tel} -> Spine T -> Op T
Iota delta = Iota' (IotaTerm delta)

(.->) : {T : Tel} -> Spine T -> Op T -> Op T
(.->) delta op = IntArr (IotaTerm delta) op

export infixr 9 .->

ExtArr : {T : Tel} -> {A : Type} -> ((a : A) -> Op T) -> Op T
ExtArr {A = a} lam = ExtArr' a lam

data Sig : (T : Tel) -> Type where
  SigEmpty : {T : Tel} -> Sig T
  (<||) : {T : Tel} -> Op T -> Sig T -> Sig T

export infixr 10 <||
```

Produces a telescope for the inputs of each operation, given a carrier type X

```idris
inputs : {T : Tel} -> (o : Op T) -> (X : Spine T -> Type) -> Tel
inputs (Iota' (IotaTerm delta)) x = Dot
inputs (IntArr (IotaTerm delta) o) x = x delta .*. (\y => inputs o x)
inputs (ExtArr' a lam) x = a .*. (\a' => inputs (lam a') x)
```

Produces a spine for telescope T of the outputs of an operation, given an input spine

```idris
outputs : {T : Tel} -> {o : Op T} -> {X : Spine T -> Type} -> (v : Spine (inputs o X)) -> Spine T
outputs {o = ExtArr' a lam} (a' .+. v') = outputs v'
outputs {o = IntArr (IotaTerm delta) o'} (x .+. v') = outputs v'
outputs {o = Iota' (IotaTerm delta)} SEmpty = delta
```

Produces a telescope for the necessary functions needed to implement the given signature

```idris
Alg : {T : Tel} -> (sig : Sig T) -> (X : Spine T -> Type) -> Tel
Alg SigEmpty x = Dot
Alg (op <|| sig) x = 
  ((v : Spine (inputs op x)) -> x (outputs v)) 
  .*. (\v => (Alg sig x))

dispInputs : {T : Tel} -> {X : Spine T -> Type} -> (op : Op T) ->
             (Y : Spine (T .**. X) -> Type) -> Tel
dispInputs (Iota' (IotaTerm delta)) y = Dot
dispInputs {X = x} (IntArr (IotaTerm delta) op) y = x delta .*. (\x' => y (delta .++. x') .*. (\y' => dispInputs op y))
dispInputs (ExtArr' a lam) y = a .*. (\a' => dispInputs (lam a') y)

dispOutputs : {T : Tel} -> {X : Spine T -> Type} -> {op : Op T} -> {Y : Spine (T .**. X) -> Type} -> 
              Spine (dispInputs {X = X} op Y) -> Spine (Alg (op <|| SigEmpty) X)  -> Spine (T .**. X)
dispOutputs {op = Iota' (IotaTerm delta)} SEmpty (alpha .+. SEmpty) = delta .++. (alpha SEmpty)
dispOutputs {op = IntArr (IotaTerm delta) op'} (x .+. y .+. mu) (alpha .+. SEmpty) = dispOutputs mu ((app alpha x) .+. SEmpty)
dispOutputs {op = ExtArr' a lam} (a' .+. mu) (alpha .+. SEmpty) = dispOutputs mu ((app alpha a') .+. SEmpty)


DisplayedAlg : {T : Tel} -> {S : Sig T} -> {X : Spine T -> Type} -> 
               (alpha : Spine (Alg S X)) -> (Y : Spine (T .**. X) -> Type) -> Tel
DisplayedAlg {S = SigEmpty} SEmpty y = Dot
DisplayedAlg {S = op <|| sig} (a .+. alpha') y = ((mu : Spine (dispInputs op y)) -> y (dispOutputs mu ?opAlgSpine)) .*. 
                 (\f => DisplayedAlg alpha' y)
```

