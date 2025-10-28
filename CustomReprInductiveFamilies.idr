module CustomReprInductiveFamilies

--- Our example to apply the theory to

import Data.Vect

%default total

data ChunkedVect : (wordSize : Nat) -> (noChunks : Nat) -> (a : Type) -> Type where
  NilCV : {wordSize : Nat} -> {a : Type} -> ChunkedVect wordSize 0 a
  Chunk : {wordSize : Nat} -> {n : Nat} -> {a : Type} -> 
          (word : Vect wordSize a) -> ChunkedVect wordSize n a -> ChunkedVect wordSize (S n) a
---

data Tel : Type where
  Dot : Tel
  (.*.) : (A : Type) -> (a : A -> Tel) -> Tel

export infixr 10 .*.

data Spine : (T : Tel) -> Type where
  SEmpty : Spine Dot
  (.+.) : {0A : Type} -> {0T : A -> Tel} ->  (a : A) -> Spine (T a) -> Spine (A .*. T)

export infixr 10 .+.

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

--- Example Tel, Operators and Sig for ChunkedVect

CVTel : Tel
CVTel = Nat .*. (\wordSize => Nat .*. (\noChunks => Type .*. (\a => Dot)))

nilOp : Op CVTel
nilOp = ExtArr (\wordSize => ExtArr (\a => Iota (wordSize .+. 0 .+. a .+. SEmpty)))
    
chunkOp : Op CVTel
chunkOp = ExtArr (\wordSize =>
            ExtArr (\noChunks =>
              ExtArr (\a =>
                ExtArr (\word : Vect wordSize a =>
                  (wordSize .+. noChunks .+. a .+. SEmpty) 
                    .-> Iota (wordSize .+. (S noChunks) .+. a .+. SEmpty)))))
 
ChunkedVectSig : Sig CVTel
ChunkedVectSig = nilOp <|| chunkOp <|| SigEmpty

---

-- Produces a telescope for the inputs of each operation, given
-- a carrier type X
inputs : {T : Tel} -> (o : Op T) -> (X : Spine T -> Type) -> Tel
inputs (Iota' (IotaTerm delta)) x = Dot
inputs (IntArr (IotaTerm delta) o) x = x delta .*. (\y => inputs o x)
inputs (ExtArr' a lam) x = a .*. (\a' => inputs (lam a') x)

-- Produces a spine for telescope T of the outputs of an operation, given an input spine
outputs : {T : Tel} -> {o : Op T} -> {X : Spine T -> Type} -> (v : Spine (inputs o X)) -> Spine T
outputs {o = ExtArr' a lam} (a' .+. v') = outputs v'
outputs {o = IntArr (IotaTerm delta) o'} (x .+. v') = outputs v'
outputs {o = Iota' (IotaTerm delta)} SEmpty = delta

-- Produces a telescope for the necessary functions needed to implement
-- the given signature
Alg : {T : Tel} -> (sig : Sig T) -> (X : Spine T -> Type) -> Tel
Alg SigEmpty x = Dot
Alg (op <|| sig) x = 
  ((v : Spine (inputs op x)) -> x (outputs v)) 
  .*. (\v => (Alg sig x))

--- Example algebras for the ChunkedVect example, using the data type declaration above as the carrier type

-- TODO: why is this not covering? There's no other possible pattern for a spine of CVTel to be...
CarrierCV : Spine CVTel -> Type
CarrierCV (wordSize .+. noChunks .+. a .+. SEmpty) =
  ChunkedVect wordSize noChunks a
CarrierCV (_ .+. _) = ?rhs1

CVAlg : Tel
CVAlg = Alg ChunkedVectSig CarrierCV

-- TODO: why is the chunk case wrong?
initialCVAlg : Spine CVAlg
initialCVAlg =
  (\(wordSize .+. a .+. SEmpty) => NilCV) .+.
  (\(wordSize .+. noChunks .+. a .+. word .+. v .+. SEmpty) => Chunk word v) .+.
  SEmpty

-- But we can also make a silly, forgetful algebra by just making all our constructors return ()

UnitCarrier : Spine CVTel -> Type
UnitCarrier _ = Unit

SillyCVAlg : Tel
SillyCVAlg = Alg ChunkedVectSig UnitCarrier

-- Forget all input information
sillyCVAlg : Spine SillyCVAlg
sillyCVAlg =
  (\nilInDelta => ()) .+.
  (\chunkInDelta => ()) .+.
  SEmpty

---

-- Insert X on the right of the telescope, (possibly) depending on previous telescope values
(.**.) : (T : Tel) -> (X : Spine T -> Type) -> Tel
(.**.) Dot x = x SEmpty .*. (\x => Dot)
(.**.) (a .*. lam) x = a .*. (\a => 
                       let
                          x' : Spine (lam a) -> Type
                          x' s = x (a .+. s)
                       in
                       (.**.) (lam a) x')

export infixl 10 .**.

-- Insert x on the right of the spine, where the type of x (possibly) depends on previous spine values
(.++.) : {T : Tel} -> {X : Spine T -> Type} -> (delta : Spine T) -> (x : X delta) -> Spine (T .**. X)
(.++.) SEmpty x = x .+. SEmpty
(.++.) (a .+. s) x = a .+. ((.++.) s x)

export infixl 10 .++.

dispInputs : {T : Tel} -> {X : Spine T -> Type} -> (op : Op T) ->
             (Y : Spine (T .**. X) -> Type) -> Tel
dispInputs (Iota' (IotaTerm delta)) y = Dot
dispInputs {X = x} (IntArr (IotaTerm delta) op) y = x delta .*. (\x' => y (delta .++. x') .*. (\y' => dispInputs op y))
dispInputs (ExtArr' a lam) y = a .*. (\a' => dispInputs (lam a') y)

app : {A : Type} -> {T : A -> Tel} -> {B : Spine (A .*. T) -> Type} -> 
     (f : (v : Spine (A .*. T)) -> B v) -> (a : A) -> (v' : Spine (T a)) -> B (a .+. v')
app f a v' = f (a .+. v')

-- TODO: why is this not covering?
dispOutputs : {T : Tel} -> {X : Spine T -> Type} -> {op : Op T} -> {Y : Spine (T .**. X) -> Type} -> 
              Spine (dispInputs {X = X} op Y) -> Spine (Alg (op <|| SigEmpty) X)  -> Spine (T .**. X)
dispOutputs {op = Iota' (IotaTerm delta)} SEmpty (alpha .+. SEmpty) = delta .++. (alpha SEmpty)
dispOutputs {op = IntArr (IotaTerm delta) op'} (x .+. y .+. mu) (alpha .+. SEmpty) = dispOutputs mu ((app alpha x) .+. SEmpty)
dispOutputs {op = ExtArr' a lam} (a' .+. mu) (alpha .+. SEmpty) = dispOutputs mu ((app alpha a') .+. SEmpty)


-- TODO: why is this not covering?
DisplayedAlg : {T : Tel} -> {S : Sig T} -> {X : Spine T -> Type} -> 
               (alpha : Spine (Alg S X)) -> (Y : Spine (T .**. X) -> Type) -> Tel
DisplayedAlg {S = SigEmpty} SEmpty y = Dot
DisplayedAlg {S = op <|| sig} (a .+. alpha') y = ((mu : Spine (dispInputs op y)) -> y (dispOutputs mu ?opAlgSpine)) .*. 
                  (\f => DisplayedAlg alpha' y)

-- Example displayed algebras for ChunkedVect

cvLength : (ChunkedVect wordSize noChunks a) -> Nat
cvLength NilCV = 0
cvLength (Chunk w cv) = length w + cvLength cv

CarrierSizeOfCV : Spine (CVTel .**. CarrierCV) -> Type
CarrierSizeOfCV (wordSize .+. noChunks .+. a .+. x .+. SEmpty) = wordSize * noChunks = cvLength x

CVDispAlg : Tel
CVDispAlg = DisplayedAlg {T = CVTel} {S = ChunkedVectSig} {X = CarrierCV} 
            initialCVAlg CarrierSizeOfCV
---
