{-# OPTIONS --erasure #-}

open Agda.Primitive

module DisplayedAlgebras where

open import Signatures
open import Algebras

DisplayedAlgOp : ∀ {n : Level} {@0 I : Tel} {@0 O : Tel}
                   {X : Spine I → Set n} {Y : Spine O → Set n} →
               (op : Op I O) →
               (αᵒ : AlgOp op X Y) →
               (Pˣ : Spine (I ** X) → Set n) →
               (Pʸ : Spine (O ** Y) → Set n) →
               Set n
DisplayedAlgOp (ι' (ιᵀ δ)) αᵒ Pˣ Pʸ = Pʸ (δ ,, αᵒ)
DisplayedAlgOp {X = X} ((ιᵀ δ) →ⁱ op) αᵒ Pˣ Pʸ = 
  (x : X δ) → Pˣ (δ ,, x) → 
  DisplayedAlgOp op (αᵒ x) Pˣ Pʸ
DisplayedAlgOp (A →ᵉ Λ) αᵒ Pˣ Pʸ = 
  (a : A) → DisplayedAlgOp (Λ a) (αᵒ a) Pˣ Pʸ


DisplayedAlg : ∀ {n : Level} {@0 I : Tel} {@0 O : Tel}
                 {Σ : Sig I O} 
                 {X : Spine I → Set n} {Y : Spine O → Set n}
               (alpha : Spine (Alg Σ X Y)) →
               (Pˣ : Spine (I ** X) → Set n) →
               (Pʸ : Spine (O ** Y) → Set n) →
               Tel {n}
DisplayedAlg {Σ = ϵ} · Pˣ Pʸ = ·
DisplayedAlg {Σ = op ◃ Σ} (αᵒ , α) Pˣ Pʸ =
  DisplayedAlgOp op αᵒ Pˣ Pʸ * (λ _ → DisplayedAlg α Pˣ Pʸ)

