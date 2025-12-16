module ApplicativeAlgebras

import Signatures
import Algebras

%default total
public export

flap : Functor f => 
       {0b : a -> Type} ->
       f ((x : a) -> b x) -> (x : a) -> f (b x)
flap fab x = map {a = (x : a) -> b x} ($ x) fab

flipDep : {0b : a -> Type} ->
          (c -> (x : a) -> b x) -> 
          (x : a) -> 
          (c -> b x)
flipDep fcab x c = fcab c x

liftAlgOp : Applicative f =>
            {0I : Tel} ->
            {0O : Tel} ->
            {o : Op I O} ->
            {x : Spine I -> Type} ->
            {y : Spine O -> Type} ->
            (falpha : f (AlgOp o x y)) ->
            AlgOp o (f . x) (f . y)
liftAlgOp {o = Iota' (IotaTerm ydelta)} falpha =
  falpha
liftAlgOp {o = IntArr (IotaTerm xdelta) o'} falpha =
  (\fx => liftAlgOp (falpha <*> fx))
liftAlgOp {o = ExtArr' a lam} {x = x} {y = y} falpha =
  (\a' : a => liftAlgOp (flap falpha a'))

data HList : List Type -> Type where
  Nil : HList []
  (:::) : {0a : Type} -> a -> HList as -> HList (a :: as)

export infixr 10 :::

sequenceHList : Applicative f =>
                {as : List Type} ->
                HList (map f as) ->
                f (HList as)
sequenceHList {as = []} Nil = pure Nil
sequenceHList {as = a :: as'} (fx ::: fxs) =
  (:::) <$> fx <*> (sequenceHList fxs)

liftAlgOpRev' : Applicative f =>
               {0I : Tel} ->
               {0O : Tel} ->
               {o : Op I O} ->
               {x : Spine I -> Type} ->
               {y : Spine O -> Type} ->
               {as : List Type} ->
               (xArgs : HList (map f as)) ->
               (falpha : f (HList as -> AlgOp o x y)) ->
               AlgOp o (f . x) (f . y)
liftAlgOpRev' {o = Iota' (IotaTerm ydelta)} xArgs falpha =
  falpha <*> (sequenceHList xArgs)
liftAlgOpRev' {o = ExtArr' a lam} xArgs falpha =
  (\a' : a => 
         liftAlgOpRev' xArgs 
            (flap (flipDep <$> falpha) a'))
liftAlgOpRev' {f = f} {o = IntArr (IotaTerm delta) o'} {as = as} xArgs falpha =
  (\fx =>
       let
         falpha' : f (HList (x delta :: as) -> AlgOp o' x y)
         falpha' = map (\alpha, hlist : HList (x delta :: as) =>
                     let
                       x ::: hlist' = hlist
                     in
                     ?alpha') 
                   falpha
       in
       liftAlgOpRev' {as = (x delta) :: as} 
          (fx ::: xArgs) falpha')

liftAlgOpRev : Applicative f =>
               {0I : Tel} ->
               {0O : Tel} ->
               {o : Op I O} ->
               {x : Spine I -> Type} ->
               {y : Spine O -> Type} ->
               (falpha : f (AlgOp o x y)) ->
               AlgOp o (f . x) (f . y)
liftAlgOpRev falpha = liftAlgOpRev' {as = []} Nil (map const falpha)

