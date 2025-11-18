module Algebras

import Signatures

%default total

public export
inputs : {0T : Tel} -> (o : Op T) -> (X : Spine T -> Type) -> Tel
inputs (Iota' (IotaTerm delta)) x = Dot
inputs (IntArr (IotaTerm delta) o) x = x delta .*. (\y => inputs o x)
inputs (ExtArr' a lam) x = a .*. (\a' => inputs (lam a') x)

public export
outputs : {0T : Tel} -> {o : Op T} -> 
          {X : Spine T -> Type} -> (v : Spine (inputs o X))
          -> Spine T
outputs {o = ExtArr' a lam} (a' .+. v') = outputs v'
outputs {o = IntArr (IotaTerm delta) o'} (x .+. v') = outputs v'
outputs {o = Iota' (IotaTerm delta)} SEmpty = delta

public export
Alg : {0T : Tel} -> (sig : Sig T) -> (X : Spine T -> Type) -> Tel
Alg SigEmpty x = Dot
Alg (op <|| sig) x = 
  ((v : Spine (inputs op x)) -> x (outputs v)) 
  .*. (\v => (Alg sig x))

