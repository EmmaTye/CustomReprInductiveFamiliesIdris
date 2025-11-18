module MonadicAlgebras

import Signatures
import Algebras

%default total

sequenceInputs : Monad m =>
                 {0T : Tel} -> 
                 {X : Spine T -> Type} ->
                 {op : Op T} ->
                 Spine (inputs op (m . X)) ->
                 m (Spine (inputs op X))
sequenceInputs {op = Iota' (IotaTerm delta)} 
               SEmpty =
                 pure SEmpty
sequenceInputs {op = IntArr (IotaTerm delta) op'} 
               (mx .+. v) =
                 do
                   x <- mx
                   map (\rest => x .+. rest) (sequenceInputs v)

sequenceInputs {op = ExtArr' a lam} (a' .+. v) =
  map (\rest => a' .+. rest) (sequenceInputs v)

eqMOutputs : Monad m =>
             {0m : Type -> Type} ->
             {0T : Tel} -> {X : Spine T -> Type} ->
             {op : Op T} ->
             (vm : Spine (inputs {T = T} op (m . X))) ->
             ((map {f = m})
                (\v =>
                   outputs {T = T} {o = op} {X = X} v = 
                     outputs {T = T} {o = op} {X = (m . X)} vm)
             (sequenceInputs {m = m} {T = T} {X = X} {op = op} vm))
eqMOutputs {op = Iota' (IotaTerm delta)} SEmpty = pure Refl
eqMOutputs {op = IntArr delta op'} (mx .+. v') = 
  ?eqMOutputsIntRhs
eqMOutputs {op = ExtArr a lam} (a' .+. v') =
  ?eqMOutputsExtRhs


mAlgebra : Monad m => 
           {0T : Tel} -> {S : Sig T} ->
           {X : Spine T -> Type} ->
           (alpha : Spine (Alg S X)) ->
           Spine (Alg S (m . X))
mAlgebra {S = SigEmpty} SEmpty = SEmpty
mAlgebra {S = op <|| sig} (alphaOp .+. alpha') =
  (\vm => do
           v <- sequenceInputs vm
           pure (alphaOp v))
  .+. (mAlgebra alpha')


