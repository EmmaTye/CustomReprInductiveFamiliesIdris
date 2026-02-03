{-# OPTIONS --erasure #-}

open Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Agda.Builtin.Sigma

-- In order to talk about induction, our input and output 
-- carrier types must be equal
module InductiveAlgebras where

open import Signatures
open import Algebras
open import DisplayedAlgebras

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

induction : ∀ {n : Level} {Δ : Tel}
              {Σ : Sig Δ Δ}
              {X : Spine Δ → Set n}
            (α : Spine (Alg Σ X X)) →
            Set (lsuc n)
induction {n = n} {Δ = Δ} {X = X} α =
  -- For any inductive algebra over α
  ∀ (P : Spine (Δ ** X) → Set n) →
    (β : Spine (DisplayedAlg α P P)) →
  -- we can constrcut a coherent section
  Σ ((x : Spine (Δ ** X)) → P x) 
    (λ σ → Spine (cohConds β σ))

InductiveAlgebra : ∀ {n : Level} {Δ : Tel {n}}
                   (Σ : Sig Δ Δ) →
                   Tel {lsuc n}
InductiveAlgebra {n = n} {Δ = Δ} Σ =
  -- carrier type X
  (Spine Δ → Set n) * (λ X →
  -- algebra α
  (Spine (Alg Σ X X)) * (λ α → 
  -- induction principle κ
  (induction α) * (λ κ → ·)))

