
TODO: 
  - example of displayed algebra
  - example of coherency proof
  - inductive algebra definition
  - representations
  - computation irrelevance of representations

# 1. Introduction

The goal of the paper (and hence this implementation) is to provide a way to have more performant run-time representations of complicated inductive families by proving that the user-given run-time representation behaves exactly like the inductive family.

As a motivating example, take the Run-Length Encoding of a list from chapter 3.2.2 of the paper Idris 2: Quantitative Type Theory in Practice by Edwin Brady:

```idris
module CustomReprInductiveFamilies
%default total

repeat : Nat -> a -> List a
repeat Z x = []
repeat (S n) x = x :: repeat n x

data RLE : {0ty : Type} -> (List ty) -> Type where
  Empty : {0ty : Type} -> RLE {ty = ty} []
  Run : {0ty : Type} -> {0ys : List ty} -> 
        (n : Nat) -> (x : ty) -> (rle : RLE ys) -> RLE (repeat (S n) x ++ ys)
```

For clarity, all the implicit arguments to the data type and the constructors are given.

This is a more performant way of expressing a `List` with consecutive values that are equal replaced with the value and a count of how many (here we define equality as being exactly the same value - `x`). However, all of our standard libraries, and indeed our way of reasoning about lists, uses the usual way of deciding what to do with the empty list, and the head of the list, instead of potentially `n` many values at a time. We could rewrite the entire standard `Data.List` library to use the run-length encoding of a list instead, and force every user to switch their mindset to this encoding, but what about when a different scenario comes up and a different form of encoding is better for performance? Do we need to rewrite the standard library for every possible encoding? And if so, how do we share code between them?

The paper in question provides a way to use the `List` data type we know and love, while being able to use a zero-cost runtime encoding of whatever we like - provided we can eliminate the runtime constructors in the same way as the `List` constructors.

We can generalise this to any inductive data structure - not just `List`s. But for this implementation, we're going to be proving that the `RLE` encoding is a well-behaved representation of `List`.

But how do we describe a general inductive data type? And indeed, how do we prove that two data types can be inducted over in the same way? We'd need to prove that they have the same algebraic structure, or "shape" as described in the paper. So we need a way to describe and prove generally:
- the algebraic structure of a data type (in our example, how would we describe a `List`'s structure)
- that an implementation of a data type follows a particular algebraic structure (that `List` does indeed follow a particular algebraic structure)
- that a representation of a data type follows the same algebraic structure (that `RLE` also follows the `List` algebraic structure)

We're using Idris2's native type system as our type theory as well as the metatheory. However, in order to describe a depdendent data type, we need some way of referencing its indices.

# 2. Algebraic Structures

In order to describe the "shape" a data type follows, we need to know
1. its indices, what it's indexing over (for `List` this is just a `Type`)
2. its operators (for `List`, this is a 'nil' operator and a 'cons' operator)

The combination of these two things produces a signature.

When we have a concrete implementation of these - i.e. a function matching each operator in the signature to a particular type, we call that an algebra.

## 2.1 Telescopes and Spines

We know that `List`'s "input" is just a `Type`, but in general we could have any number of indices. Look at `RLE` - this data type has both a(n implicit) `ty : Type` and a `List ty`. Its list "input" depends on the value of the previous input. So we need a way to generalise these lists of dependent 

Idris2 does give us a way to describe dependent pairs using the `**` sugar. So we could use that data type as our indices for a type, for example the `List` and `RLE` types could be written using a dependent pair like:

```idris
depPairToList : (ty : Type ** Unit) -> Type
depPairToList (ty ** ()) = List ty

depPairToRLE : (ty : Type ** List ty) -> Type
depPairToRLE (ty ** xs) = RLE {ty = ty} xs
```

But we want to be able to talk about any given inductively defined family of data types. How do we abstract this to talk about _any_ such dependent pair? Or a finitely long nested sequence of dependent pairs? Idris2 doesn't give us an abstraction over any dependent pair, so this part of the theory we'll have to construct ourselves.

A finitely long nested sequence of dependent pairs is called a telescope. For example, `(ty : Type ** List ty)` is a telescope, but so is just `ty : Type` - a telescope can have any length. In general, a telescope is a dependent sequence of the form `(x0 : T0 ** x1 : T1(x0) ** x2 : T2(x0, x1) ** ... xn : Tn(x0, ..., x{n-1}))`.

Below we've defined `Tel` as a nested sequence of types, which can possibly depend on previous types in the sequence:

```idris
data Tel : Type where
  Dot : Tel
  (.*.) : (A : Type) -> (a : A -> Tel) -> Tel

export infixr 10 .*.
```

So our `List` and `RLE` indices would be represented as the telescope

```idris
ListTel : Tel
ListTel = Type .*. (\ty => Dot)

RLETel : Tel
RLETel = Type .*. (\ty => List ty .*. (\l => Dot))
```

But how do we get an actual instance of these telescopes? For example, in Idris2 the terms for a dependent pair are overloaded with the type construction `**`, so we can write the following correctly typed code:

```idris
rleDepPairExample : (ty : Type ** List ty)
rleDepPairExample = (Int ** [1])
```

An instance of a telescope is called a spine. We can define our a spine of a particular telescope as following:

```idris
data Spine : (T : Tel) -> Type where
  SEmpty : Spine Dot
  (.+.) : {0A : Type} -> {0T : A -> Tel} ->  (a : A) -> Spine (T a) -> Spine (A .*. T)

export infixr 10 .+.
```

We've chosen not to overload the telescope and spine constructors (like Idris2's dependent pairs) for clarity.

Example spines of the `ListTel` and `RLETel` could be

```idris
listSpineExample : Spine ListTel
listSpineExample = Int .+. SEmpty

rleSpineExample : Spine RLETel
rleSpineExample = Int .+. [1] .+. SEmpty
```

We can convert between a spine of a type's indices and the actual Idris2-defined data type by the following functions:

```idris
spineToList : Spine ListTel -> Type
spineToList (ty .+. SEmpty) = List ty

spineToRLE : Spine RLETel -> Type
spineToRLE (ty .+. xs .+. SEmpty) = RLE {ty = ty} xs
```

Note that these `spineTo<DataType>` functions are injective - we don't have a way of expressing that two data types with different indices are the same. In general, we call these "spine-to-data-type" functions iota, to reflect the injectivity.

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

- Given a(n implicit) family `B`, a function `f` to construct a `B`, and a term `a` for the first element of `B`'s indices, return a function `f` to construct a `B` with the first input as `a`:

```idris
app : {0A : Type} -> {0T : A -> Tel} -> {0B : Spine (A .*. T) -> Type} -> 
     (f : (v : Spine (A .*. T)) -> B v) -> (a : A) -> (v' : Spine (T a)) -> B (a .+. v')
app f a v' = f (a .+. v')
```

## 2.2 Signatures

We've described how to generalise the indices to a data type, but what about the operators?

Let's take the constructors from `List` as examples. The "shape" of this constructor takes a(n implicit) type, and returns a `List` (of the implicit type). We can think of this then as a "function" which takes a type and returns an element of the signature we're defining:

```
Nil : (ty : Type) -> iota ty
```

We're using iota here to reference ourselves - the whole point of the generalisation is _not_ to tie us to a specific type, so we don't always want to return a `List ty`. But for whatever type we're using to implement our signature, we want the `Nil` operator to return an element of it.

In a similar manner, `Cons` takes a(n implicit) type, an element of that type, a previous element of our signature and returns an element of our signature. We can then think of this as a "function" of the form:

```
Cons : (ty : Type) -> ty -> iota ty -> iota ty
```

So operators can be thought of as functions, from either "external types", like `ty : Type` and `ty` itself, or "internal types", meaning the signature we're defining (iota).

To make sure our operators are positive by construction - that iota doesn't appear as an input to a function used in the operator - we can describe our possible operators as follows:

```idris
data OpTerm : (T : Tel) -> Type where
  IotaTerm : {T : Tel} -> Spine T -> OpTerm T

data Op : (T : Tel) -> Type where
  Iota' : {T : Tel} -> OpTerm T -> Op T
  IntArr : {T : Tel} -> OpTerm T -> Op T -> Op T
  ExtArr' : {T : Tel} -> (A : Type) -> ((a : A) -> Op T) -> Op T
```

In order to help write operators more succintly, we introduce the following helpers:

```idris
Iota : {T : Tel} -> Spine T -> Op T
Iota delta = Iota' (IotaTerm delta)

(.->) : {T : Tel} -> Spine T -> Op T -> Op T
(.->) delta op = IntArr (IotaTerm delta) op

export infixr 9 .->

ExtArr : {T : Tel} -> {A : Type} -> ((a : A) -> Op T) -> Op T
ExtArr {A = a} lam = ExtArr' a lam
```

Our `Nil` and `Cons` operators using this language would be:

```idris
nilOp : Op ListTel
nilOp = ExtArr (\ty : Type => Iota (ty .+. SEmpty))

consOp : Op ListTel
consOp = ExtArr (\ty : Type =>
           (ExtArr (\x : ty =>
             (ty .+. SEmpty .-> Iota (ty .+. SEmpty)))))
```

Now we can define our signature over a telescope of indices as a sequence of operators for those indices:

```idris
data Sig : (T : Tel) -> Type where
  SigEmpty : {T : Tel} -> Sig T
  (<||) : {T : Tel} -> Op T -> Sig T -> Sig T

export infixr 10 <||
```

The hard part of defining the `List` input telescope and operators is done, so we can define our `List` signature as follows:

```idris
ListSig : Sig ListTel
ListSig = nilOp <|| consOp <|| SigEmpty
```

## 2.3 Algebras

We now have an abstract way to talk about a data type's signature - its input telescope and operators. But the Idris2 `List` data type is an _implementation_ of this signature - `Nil` is a concrete constructor that follows the structure of the `nilOp`, and respectively for `Cons`. But, formally, what does "following the structure" of an operator mean? How do we define an "implementation" of a signature?

We call the implementation of a signature an algebra. An algebra consists of a carrier type - what to replace the `Iota`'s with, in the example the `List` type - and functions that correspond to the operators of a signature that return an element of the carrier type. Note that for this definition, the carrier type must have the same indices as the signature.

First off, let's build up our operator function implementation. We can see that the `Nil` constructor from `List`:
```
Nil : (ty : Type) -> List ty
```
looks like a function from a `Type` to a `List` of that type.

The `Cons` constructor in an uncurried format:
```
Cons : (ty : Type ** x : ty ** xs : List ty) -> List ty
```
can be viewed as a function that takes a spine of a `Type`, a value of that type, a previous `List` of that type and returns another `List` of the type.

In general, an implementation of an operator can be seen as a function that takes a spine of inputs (corresponding to the `IntArr`s and `ExtArr`s) and produces an element of the carrier type applied to the final Iota spine.

To help us write this, we have the below `inputs` function that produces a telescope for the inputs of each operation, given a carrier type `X` (i.e. the type of the uncurried "input"s to an operator):

```idris
inputs : {0T : Tel} -> (o : Op T) -> (X : Spine T -> Type) -> Tel
inputs (Iota' (IotaTerm delta)) x = Dot
inputs (IntArr (IotaTerm delta) o) x = x delta .*. (\y => inputs o x)
inputs (ExtArr' a lam) x = a .*. (\a' => inputs (lam a') x)
```

And the `outputs` function which just extracts the returned indices to our carrier type:

```idris
outputs : {T : Tel} -> {o : Op T} -> {X : Spine T -> Type} -> (v : Spine (inputs o X)) -> Spine T
outputs {o = ExtArr' a lam} (a' .+. v') = outputs v'
outputs {o = IntArr (IotaTerm delta) o'} (x .+. v') = outputs v'
outputs {o = Iota' (IotaTerm delta)} SEmpty = delta
```

So now we can say that an algebra for a signature over a carrier type is a sequence (a spine) of functions for each operatorin the signature from the `inputs` of that operator to its `outputs`:

```idris
Alg : {T : Tel} -> (sig : Sig T) -> (X : Spine T -> Type) -> Tel
Alg SigEmpty x = Dot
Alg (op <|| sig) x = 
  ((v : Spine (inputs op x)) -> x (outputs v)) 
  .*. (\v => (Alg sig x))
```

Using Idris2's `List` type as our carrier, we can define an algebra for it as:

```idris
CarrierList : Spine ListTel -> Type
CarrierList (ty .+. SEmpty) = List ty

listAlg : Spine (Alg ListSig CarrierList)
listAlg =
  let
  nilFn : (v : Spine (inputs NilOp CarrierList)) -> 
          CarrierList (outputs {o = NilOp} v)
  nilFn = (\(ty .+. SEmpty) => [])
  consFn : (v : Spine (inputs ConsOp CarrierList)) -> 
           CarrierList (outputs {o = ConsOp} {X = CarrierList} v)
  consFn = (\(ty .+. x .+. xs .+. SEmpty) => x :: xs)
  in
  nilFn
  .+.
  consFn
  .+.
  SEmpty
```

# 4. Induction

## 4.1 Shape of algebras

We now have a way to talk about abstract signatures, and algebras that implement them. We might even think that `listAlg` is the only way to implement our signature - how else can we get the shape of our operators? However, there's no constraint on the returned value other than that it must have the correct type. We can forget our input information as we wish. In fact, our `consFn` could just return the empty list:

```idris
emptyConsFn : (v : Spine (inputs ConsOp CarrierList)) -> 
         CarrierList (outputs {o = ConsOp} {X = CarrierList} v)
emptyConsFn = (\(ty .+. x .+. xs .+. SEmpty) => [])
```

We could go one step further - we could let our carrier type be `Unit` so that every operator, no matter the signature, must forget all information:

```idris
CarrierUnit : {0T : Tel} -> Spine T -> Type
CarrierUnit delta = Unit

unitAlg : {0T : Tel} -> (sig : Sig T) -> Spine (Alg sig CarrierUnit)
unitAlg SigEmpty = SEmpty
unitAlg (o <|| sig) =
  (\opInputs => ()) .+. (unitAlg sig)
```

But the whole point of being able to switch between different representations of an inductive type is to make sure we aren't loosing information! What we want to describe is an algebra that looses no information - called an initial algebra.

Another way to state that an algebra is initial is that it supports an induction principle. For lists, this would be equivalent to saying that, for any property `P` of lists, if we can
1. prove `P` for the empty list
2. assuming `P` holds for `xs`, and given any `x`, prove `P (x :: xs)`
then we can prove that `P` holds for every list.

This is equivalent to being able to construct a function of type:

```idris
listInduction : (A : Type) -> (P : List A -> Type) -> 
                P [] -> 
                ((x : A) -> (xs : List A) -> P xs -> P (x :: xs)) -> 
                (xs : List A) -> P xs
```

We extend this induction property to any algebra of the `ListSig` by replacing the `List` with the carrier type for that algebra, and the constructors with the functions for the respective operators (`nilFn` and `consFn`):

```
listAlgInduction : (X : Spine ListTel -> Type) ->
                   (P : Spine (ListTel .**. X) -> Type) ->
                   (nilCase : (ty : Type) -> P (ty .+. nilFn ty)) ->
                   (consCase : (ty : Type) -> (x : ty) -> (xs : X ty) -> P (ty .+. xs) -> P (ty .+. consFn ty x xs)) ->
                   (ty : Type) -> (xs : X ty) -> P (ty .+. xs)

```
(note that above we've removed the `SEmpty`'s for succintness)

However, our silly `unitAlg` would still satisfy this by just using the `nilCase` for all `xs`:

```idris
unitInduction : (P : (Type, Unit) -> Type) ->
                (nilCase : (ty : Type) -> P (ty, ())) ->
                (consCase : (ty : Type) -> (x : ty) -> (xs : Unit) -> P (ty, xs) -> P (ty, ())) ->
                (ty : Type) -> (xs : Unit) -> P (ty, xs)
unitInduction p nilCase consCase ty () = nilCase ty
```
(note that above we've replaced the telescope/spine syntax with tuples for succintness.)

We call the returned function from the partially applied `unitInduction` given `P`, `nilCase`, `consCase`, and `ty`, a section, and usually use `sigma` to denote it:
```
sigma : (xs : Unit) -> P (ty, xs)
```

We need an additional condition on the result of our induction principle - that the returned `sigma(xs)` uses the respective inductive case for each operator in the algebra. That is:

```
sigma(nilFn ty) = nilCase ty
sigma(consFn ty x xs) = consCase ty x xs sigma(xs)
```

These are called coherence conditions.

Now we can say that our `unitAlg` does _not_ satisfy these coherence conditions - and is hence not an initial algebra for `ListSig`. For example, take:

```idris
PUnit : Type -> Unit -> Type
PUnit ty () = Nat

nilCase : (ty : Type) -> PUnit ty ()
nilCase ty = 1

consCase : (ty : Type) -> (x : ty) -> (xs : Unit) -> 
           PUnit ty xs -> PUnit ty ()
consCase ty x () prev = 3
```

Now this satisfies the previous induction principle - we can provide a value of type `PUnit ty xs` for all `ty : Type` and `xs : Unit` by using the `nilCase` of `1`. However, this doesn't satisfy the coherence conditions - 
```
sigma(consFn ty x xs)  = sigma(()) 
                       = 1
                      /= consCase ty x xs sigma(xs)
                      /= 3
```
Here, we say that this section `sigma` is not coherent.

But the section that uses the `consCase` instead in our definition of `unitInduction` also wouldn't be coherent, since it wouldn't satisfy the conditions for `nilFn`. So there is no section for `PUnit`, `nilCase` and `consCase` which would satisfy the coherence conditions.

So we want to constrain our algebras to ones on which we can provide a coherent section for any `P` and case statements - i.e. that have a coherent induction principle. We call these inductive algebras.

But how do we talk generally about "case statements" for a property `P : X -> Type`? In fact, these "case statements" are actually another algebra for the original signature, this time with the carrier being `P` instead of `X`. From the type of the induction principle, the indices into `P` for our algebra functions must be computed from the original algebraic functions. For our list signature, the algebra for `P` must satisfy:
```
nilFnP (ty .+. SEmpty) : P (nilFn ty)

consFnP (ty .+. x .+. xs .+. ps .+. SEmpty) : P (consFn ty x xs)
```
where `ps : P (xs)`. Whenever we see a recursive instance of our operator - here the `xs` - we also add a recursive instance of `P(xs)`.

An algebra for a signature constructed from the induction cases for another algebra is called a displayed algebra. In this case, the algebra `(P, nilFnP, consFnP)` would be a displayed algebra over `(X, nilFn, consFn)`.

Now that we can say that our case statements for particular property and an induction principle on an algebra is a displayed algebra over that algebra, we can set our goal for the inductive algebras we want to target:

An algebra `(x, alpha)` is inductive if and only if for any displayed algebra `(P, beta)`, we can construct a coherent section for it. That is, there exists a `sigma : (x : X) -> P(x)` such that for every operator `O` of the signature, the following is satisfied:
```
sigma(alpha.O <params>) = beta.O <params'>
```
where `params'` is the sequence of parameters `params`, with any recursive instance `x` replaced with `x .+. sigma(x)`.

## 4.2 Displayed algebras

Let's define what is means to be a displayed algebra for a signature over a particular algebra.

From our earlier definition of an algebra, we need to provide a function for each operator, that takes a spine of inputs corresponding to the `IntArr`s and `ExtArr`s and produces an element of the carrier type. However in this case, our carrier type doesn't have the same indices as our signature - it has an extra one, `X`. So in order to provide all the indices needed for our recursive inputs and our return type, we need an extra parameter of `x : X` for any recursive `Iota delta` call.

In a similar fashion to how the original `inputs` function was defined, the below `dispInputs` function produces a telescope for the inputs to the displayed algebra of each operation in the original signature:

```idris
dispInputs : {0T : Tel} -> {X : Spine T -> Type} -> 
             (op : Op T) -> (P : Spine (T .**. X) -> Type) ->
             Tel
dispInputs (Iota' (IotaTerm delta)) y = Dot
dispInputs {X = x} (IntArr (IotaTerm delta) op) p = 
  x delta .*. 
  (\x' => p (delta .++. x') .*. 
         (\p' => dispInputs op p))
dispInputs (ExtArr' a lam) p = 
  a .*. (\a' => dispInputs (lam a') p)
```

The only difference between `inputs` and `dispInputs` is in the `IntArr` case, where we provide an `x : X delta` and a `p : P (delta .++. x)` for our recursive cases.

As for our `outputs`, our `dispOutputs` just returns the spine of the resulting indices:

```idris
dispOutputs : {0T : Tel} -> {X : Spine T -> Type} -> 
              {op : Op T} -> {Y : Spine (T .**. X) -> Type} ->
              Spine (dispInputs {X = X} op Y) -> 
              Spine (Alg (op <|| SigEmpty) X) -> 
              Spine (T .**. X)
dispOutputs {op = Iota' (IotaTerm delta)} 
            SEmpty (alphaOp .+. SEmpty) = 
              delta .++. (alphaOp SEmpty)
dispOutputs {op = IntArr (IotaTerm delta) op'} 
            (x .+. y .+. mu) (alpha .+. SEmpty) = 
              dispOutputs mu ((app alpha x) .+. SEmpty)
dispOutputs {op = ExtArr' a lam} 
            (a' .+. mu) (alpha .+. SEmpty) = 
              dispOutputs mu ((app alpha a') .+. SEmpty)
```

So now we can say that a displayed algebra over an algebra `alpha` is a sequence (a spine) of functions for each operator in the signture from the `dispInputs` of that operator to its `dispOutputs`:
```idris
DisplayedAlg : {0T : Tel} -> {S : Sig T} -> 
               {X : Spine T -> Type} -> 
               (alpha : Spine (Alg S X)) -> 
               (P : Spine (T .**. X) -> Type) -> Tel
DisplayedAlg {S = SigEmpty} SEmpty p = Dot
DisplayedAlg {S = op <|| sig} (alphaOp .+. alpha') p = 
  ((mu : Spine (dispInputs op p)) -> 
   p (dispOutputs mu (alphaOp .+. SEmpty))) 
  .*. (\f => DisplayedAlg alpha' p)
```

