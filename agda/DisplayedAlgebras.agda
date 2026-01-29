{-# OPTIONS --erasure #-}

open Agda.Primitive

module DisplayedAlgebras where

open import Signatures
open import Algebras

dispInputs : ∀ {n : Level} {@0 I : Tel} {@0 O : Tel} 
               {X : Spine I → Set n} →
             (op : Op I O) → (Pˣ : Spine (I ** X) → Set n) →
             Tel {n}
dispInputs (ι' (ιᵀ δ)) Pˣ = ·
dispInputs {X = X} ((ιᵀ δ) →ⁱ op) Pˣ =
  X δ * (λ x → Pˣ (δ ,, x) * (λ px → dispInputs op Pˣ))
dispInputs (A →ᵉ Λ) Pˣ =
  A * (λ a → dispInputs (Λ a) Pˣ)

dispOutputs : ∀ {n : Level} {@0 I : Tel} {@0 O : Tel}
                {op : Op I O}
                {X : Spine I → Set n} {Y : Spine O → Set n}
                {Pˣ : Spine (I ** X) → Set n}
                {Pʸ : Spine (O ** Y) → Set n} →
              Spine (dispInputs op Pˣ) →
              AlgOp op X Y → Spine (O ** Y)
dispOutputs {op = ι' (ιᵀ δ)} · αᵒ = δ ,, αᵒ
dispOutputs {op = (ιᵀ δ) →ⁱ op} {Pʸ = Pʸ} (x , (px , μ)) αᵒ =
  dispOutputs {Pʸ = Pʸ} μ (αᵒ x)
dispOutputs {op = A →ᵉ Λ} {Pʸ = Pʸ} (a , μ) αᵒ =
  dispOutputs {Pʸ = Pʸ} μ (αᵒ a)

DisplayedAlg : ∀ {n : Level} {@0 I : Tel} {@0 O : Tel}
                 {Σ : Sig I O} 
                 {X : Spine I → Set n} {Y : Spine O → Set n}
                 (alpha : Spine (Alg Σ X Y)) →
                 (Pˣ : Spine (I ** X) → Set n) →
                 (Pʸ : Spine (O ** Y) → Set n) →
                 Tel {lsuc n}
DisplayedAlg {Σ = ϵ} · Pˣ Pʸ = ·
DisplayedAlg {Σ = op ◃ Σ} (αᵒ , α) Pˣ Pʸ =
  ((μ : Spine (dispInputs op Pˣ)) → 
   Pʸ (dispOutputs {Pʸ = Pʸ} μ αᵒ)) *
  (λ Λ → DisplayedAlg α Pˣ Pʸ)

