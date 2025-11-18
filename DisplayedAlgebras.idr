module DisplayedAlgebras

import Signatures
import Algebras

%default total

public export
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

public export
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

public export
DisplayedAlg : {0T : Tel} -> {S : Sig T} -> 
               {X : Spine T -> Type} -> 
               (alpha : Spine (Alg S X)) -> 
               (P : Spine (T .**. X) -> Type) -> Tel
DisplayedAlg {S = SigEmpty} SEmpty p = Dot
DisplayedAlg {S = op <|| sig} (alphaOp .+. alpha') p = 
  ((mu : Spine (dispInputs op p)) -> 
   p (dispOutputs mu (alphaOp .+. SEmpty))) 
  .*. (\f => DisplayedAlg alpha' p)

--- Coherence conds

public export
inputsToDispInputs : {0T : Tel} ->
                     {X : Spine T -> Type} ->
                     {P : Spine (T .**. X) -> Type} ->
                     {op : Op T} ->
                     (v : Spine (inputs op X)) ->
                     (sigma : (x : Spine (T .**. X)) -> P x) ->
                         Spine (dispInputs {X = X} op P)
inputsToDispInputs {op = Iota' (IotaTerm delta)} 
                   SEmpty sigma = SEmpty
inputsToDispInputs {op = IntArr (IotaTerm delta) op'} 
                   (x .+. v) sigma = 
                     x .+. sigma (delta .++. x) .+. 
                     inputsToDispInputs v sigma
inputsToDispInputs {op = ExtArr' a lam} 
                   (a' .+. v) sigma = 
                     a' .+. inputsToDispInputs v sigma

public export
CoherenceConds : {0T : Tel} -> {S : Sig T} ->
                 {X : Spine T -> Type} ->
                 {P : Spine (T .**. X) -> Type} ->
                 {alpha : Spine (Alg S X)} ->
                 (beta : Spine (DisplayedAlg {S = S} {X = X} alpha P)) ->
                 (sigma : (x : Spine (T .**. X)) -> P x) ->
                 Tel
-- CoherenceConds {S = SigEmpty} {alpha = SEmpty} 
--                SEmpty sigma = Dot
-- CoherenceConds {S = op <|| sig} {X = x} {alpha = a .+. alpha'} 
--                (b .+. beta') sigma = 
--                  ((v : Spine (inputs op x)) -> 
--                   sigma ((outputs v) .++. (a v)) 
--                   = b (inputsToDispInputs v sigma)) 
--                  .*. (\refl => CoherenceConds beta' sigma)


