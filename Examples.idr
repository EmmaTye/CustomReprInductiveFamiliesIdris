module Examples

import Signatures
import Algebras

%default total

-- RLE definition

repeat : Nat -> a -> List a
repeat Z x = []
repeat (S n) x = x :: repeat n x

data RLE : {0ty : Type} -> (List ty) -> Type where
  Empty : {0ty : Type} -> RLE {ty = ty} []
  Run : {0ty : Type} -> {0ys : List ty} -> 
        (n : Nat) -> (x : ty) -> (rle : RLE ys) -> RLE (repeat (S n) x ++ ys)

depPairToRLE : (ty : Type ** List ty) -> Type
depPairToRLE (ty ** xs) = RLE {ty = ty} xs

depPairToList : (ty : Type ** Unit) -> Type
depPairToList (ty ** ()) = List ty

rleDepPairExample : (ty : Type ** List ty)
rleDepPairExample = (Int ** [1])

--- Example telescopes/spines

ListTel : Tel
ListTel = Type .*. (\ty => Dot)

RLETel : Tel
RLETel = Type .*. (\ty => List ty .*. (\l => Dot))

listSpineExample : Spine ListTel
listSpineExample = Int .+. SEmpty

rleSpineExample : Spine RLETel
rleSpineExample = Int .+. [1] .+. SEmpty

spineToList : Spine ListTel -> Type
spineToList (ty .+. SEmpty) = List ty

spineToRLE : Spine RLETel -> Type
spineToRLE (ty .+. xs .+. SEmpty) = RLE {ty = ty} xs

--- Example list signature

NilOp : Op ListTel
NilOp = ExtArr (\ty : Type => Iota (ty .+. SEmpty))

ConsOp : Op ListTel
ConsOp = ExtArr (\ty : Type =>
           (ExtArr (\x : ty =>
             (ty .+. SEmpty .-> Iota (ty .+. SEmpty)))))


ListSig : Sig ListTel
ListSig = NilOp <|| ConsOp <|| SigEmpty

--- List example algebra

CarrierList : Spine ListTel -> Type
CarrierList (ty .+. SEmpty) = List ty

listAlg : Spine (Alg ListSig CarrierList)
listAlg =
  let
  nilFn : (v : Spine (inputs {T = ListTel} NilOp CarrierList)) -> 
          CarrierList (outputs {T = ListTel} {o = NilOp} {X = CarrierList} v)
  nilFn = (\(ty .+. SEmpty)  => [])
  consFn : (v : Spine (inputs ConsOp CarrierList)) -> 
           CarrierList (outputs {o = ConsOp} {X = CarrierList} v)
  consFn = (\(ty .+. x .+. xs .+. SEmpty) => x :: xs)
  in
  nilFn
  .+.
  consFn
  .+.
  SEmpty

emptyConsFn : (v : Spine (inputs ConsOp CarrierList)) -> 
         CarrierList (outputs {o = ConsOp} {X = CarrierList} v)
emptyConsFn = (\(ty .+. x .+. xs .+. SEmpty) => [])

--- Trivial unit algebras

CarrierUnit : {0T : Tel} -> Spine T -> Type
CarrierUnit delta = Unit

unitAlg : {0T : Tel} -> (sig : Sig T) -> Spine (Alg sig CarrierUnit)
unitAlg SigEmpty = SEmpty
unitAlg (o <|| sig) =
  (\opInputs => ()) .+. (unitAlg sig)

listInduction : (A : Type) -> (P : List A -> Type) -> 
                P [] -> 
                ((x : A) -> (xs : List A) -> P xs -> P (x :: xs)) -> 
                (xs : List A) -> P xs

unitInduction : (P : (Type, Unit) -> Type) ->
                (nilCase : (ty : Type) -> P (ty, ())) ->
                (consCase : (ty : Type) -> (x : ty) -> (xs : Unit) -> P (ty, xs) -> P (ty, ())) ->
                (ty : Type) -> (xs : Unit) -> P (ty, xs)
unitInduction p nilCase consCase ty () = nilCase ty

PUnit : Type -> Unit -> Type
PUnit ty () = Nat

nilCase : (ty : Type) -> PUnit ty ()
nilCase ty = 1

consCase : (ty : Type) -> (x : ty) -> (xs : Unit) -> 
           PUnit ty xs -> PUnit ty ()
consCase ty x () prev = 3

