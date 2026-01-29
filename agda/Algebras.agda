{-# OPTIONS --erasure #-}

open import Agda.Primitive

module Algebras where

open import Signatures

AlgOp : ∀ {n : Level} {@0 I : Tel {n}} {@0 O : Tel} → 
        Op I O → (X : Spine I → Set n) → 
        (Y : Spine O → Set n) →
        Set n
AlgOp (ι' (ιᵀ δ)) X Y = Y δ
AlgOp ((ιᵀ δ) →ⁱ op) X Y = X δ → AlgOp op X Y
AlgOp (A →ᵉ Λ) X Y = (a : A) → AlgOp (Λ a) X Y

Alg : ∀  {n : Level} {@0 I : Tel} {@0 O : Tel} → 
      (Σ : Sig I O) → (X : Spine I → Set n) → 
      (Y : Spine O → Set n) →
      Tel {n}
Alg ϵ X Y = ·
Alg (op ◃ Σ) X Y = AlgOp op X Y * (λ v → Alg Σ X Y)

