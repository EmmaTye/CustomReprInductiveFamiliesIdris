module Algebras

import Signatures

%default total

public export
AlgOp : {0I : Tel} -> {0O : Tel} -> (o : Op I O) -> 
        (X : Spine I -> Type) ->
        (Y : Spine O -> Type) ->
        Type
AlgOp (Iota' (IotaTerm delta)) x y = y delta
AlgOp (ExtArr' a lam) x y = (a' : a) -> AlgOp (lam a') x y
AlgOp (IntArr (IotaTerm delta) o') x y = x delta -> 
                                         AlgOp o' x y

public export
Alg : {0I : Tel} -> {0O : Tel} -> (sig : Sig I O) -> 
      (X : Spine I -> Type) -> 
      (Y : Spine O -> Type) ->
      Tel
Alg SigEmpty x y = Dot
Alg (o <|| sig) x y =
  AlgOp o x y
  .*. (\v => (Alg sig x y))

