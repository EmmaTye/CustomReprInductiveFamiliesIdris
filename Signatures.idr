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
data Op : (I : Tel) -> (O : Tel) -> Type where
  Iota' : {0I : Tel} -> {0O : Tel} -> OpTerm O -> Op I O
  IntArr : {0I : Tel} -> {0O : Tel} -> OpTerm I -> Op I O -> 
           Op I O
  ExtArr' : {0I : Tel} -> {0O : Tel} -> (A : Type) -> 
            ((a : A) -> Op I O) -> Op I O

public export
Iota : {0I : Tel} -> {O : Tel} -> Spine O -> Op I O
Iota delta = Iota' (IotaTerm delta)

public export
(.->) : {I : Tel} -> {0O : Tel} -> Spine I -> Op I O -> Op I O
(.->) delta op = IntArr (IotaTerm delta) op

export infixr 9 .->

public export
ExtArr : {0I : Tel} -> {0O : Tel} -> {A : Type} -> ((a : A) -> Op I O) -> Op  I O
ExtArr {A = a} lam = ExtArr' a lam

public export
data Sig : (I : Tel) -> (O : Tel) -> Type where
  SigEmpty : {0I : Tel} -> {0O : Tel} -> Sig I O
  (<||) : {0I : Tel} -> {0O : Tel} -> Op I O -> Sig I O -> 
          Sig I O

export infixr 10 <||

