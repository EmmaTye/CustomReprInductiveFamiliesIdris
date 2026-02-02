{-# OPTIONS --erasure #-}

open Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

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

-- In order to talk about induction, our input and outputs carrier types
-- must be equal
cohCondsOp : ∀ {n : Level} {@0 Δ : Tel}
               {X : Spine Δ → Set n}
               {op : Op Δ Δ}
               {P : Spine (Δ ** X) → Set n}
             (αᵒ : AlgOp op X X)
             (βᵒ : DisplayedAlgOp op αᵒ P P) →
             (σ : (x : Spine (Δ ** X)) → P x) →
             Set n
cohCondsOp {op = ι' (ιᵀ δ)} αᵒ βᵒ σ =
  σ (δ ,, αᵒ) ≡ βᵒ
cohCondsOp {X = X} {op = (ιᵀ δ) →ⁱ op} αᵒ βᵒ σ =
  (x : X δ) → cohCondsOp {op = op} (αᵒ x)
                         (βᵒ x (σ (δ ,, x))) σ
cohCondsOp {op = A →ᵉ Λ} αᵒ βᵒ σ =
  (a : A) → cohCondsOp {op = Λ a} (αᵒ a) (βᵒ a) σ

cohConds : ∀ {n : Level} {@0 Δ : Tel}
             {Σ : Sig Δ Δ}
             {X : Spine Δ → Set n}
             {α : Spine (Alg Σ X X)}
             {P : Spine (Δ ** X) → Set n}
           (β : Spine (DisplayedAlg α P P)) →
           (σ : (x : Spine (Δ ** X)) → P x) →
           Tel {n}
cohConds {Σ = ϵ} {α = ·} · σ = ·
cohConds {Σ = op ◃ Σ} {α = αᵒ , α} (βᵒ , β) σ =
  (cohCondsOp {op = op} αᵒ βᵒ σ)
  * (λ _ → (cohConds β σ))
