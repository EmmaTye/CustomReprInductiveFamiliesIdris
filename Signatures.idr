module Signatures
%default total

--- Telescopes

public export
data Tel : Type where
  Dot : Tel
  (.*.) : (A : Type) -> (a : A -> Tel) -> Tel

export infixr 10 .*.

public export
data Spine : (T : Tel) -> Type where
  SEmpty : Spine Dot
  (.+.) : {0A : Type} -> {0T : A -> Tel} -> (a : A) -> Spine (T a) -> Spine (A .*. T)

export infixr 10 .+.

public export
(.**.) : (T : Tel) -> (X : Spine T -> Type) -> Tel
(.**.) Dot x = x SEmpty .*. (\x => Dot)
(.**.) (a .*. lam) x = a .*. (\a => 
                       let
                          x' : Spine (lam a) -> Type
                          x' s = x (a .+. s)
                       in
                       (.**.) (lam a) x')

export infixl 10 .**.

public export
(.++.) : {T : Tel} -> {X : Spine T -> Type} -> (delta : Spine T) -> (x : X delta) -> Spine (T .**. X)
(.++.) SEmpty x = x .+. SEmpty
(.++.) (a .+. s) x = a .+. ((.++.) s x)

export infixl 10 .++.

public export
app : {0A : Type} -> {0T : A -> Tel} -> {0B : Spine (A .*. T) -> Type} -> 
     (f : (v : Spine (A .*. T)) -> B v) -> (a : A) -> (v' : Spine (T a)) -> B (a .+. v')
app f a v' = f (a .+. v')

--- Signatures

public export
data OpTerm : (T : Tel) -> Type where
  IotaTerm : {T : Tel} -> Spine T -> OpTerm T

public export
data Op : (T : Tel) -> Type where
  Iota' : {0T : Tel} -> OpTerm T -> Op T
  IntArr : {0T : Tel} -> OpTerm T -> Op T -> Op T
  ExtArr' : {0T : Tel} -> (A : Type) -> ((a : A) -> Op T) -> Op T

public export
Iota : {T : Tel} -> Spine T -> Op T
Iota delta = Iota' (IotaTerm delta)

public export
(.->) : {T : Tel} -> Spine T -> Op T -> Op T
(.->) delta op = IntArr (IotaTerm delta) op

export infixr 9 .->

public export
ExtArr : {T : Tel} -> {A : Type} -> ((a : A) -> Op T) -> Op T
ExtArr {A = a} lam = ExtArr' a lam

public export
data Sig : (T : Tel) -> Type where
  SigEmpty : {T : Tel} -> Sig T
  (<||) : {T : Tel} -> Op T -> Sig T -> Sig T

export infixr 10 <||

