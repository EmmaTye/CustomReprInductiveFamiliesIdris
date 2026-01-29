{-# OPTIONS --erasure #-}

open Agda.Primitive

module Signatures where

data Tel {n : Level} : Set (lsuc n)  where
  · : Tel
  _*_ : (A : Set n) → (A → Tel {n}) → Tel {n}

data Spine {n : Level} : Tel -> Set (lsuc n) where
  · : Spine ·
  _,_ : ∀ {@0 A : Set n} {@0 Δ : A → Tel} →
        (a : A) → Spine (Δ a) → Spine (A * Δ)

_**_ : ∀ {n : Level} (Δ : Tel) → (X : Spine Δ → Set n) → Tel {n}
· ** X = X · * (λ x → ·)
_**_ {n = n} (A * Δ) X = 
  A * (λ A → 
    let
      X' : Spine (Δ A) → Set n
      X' δ = X (A , δ)
    in
    (Δ A) ** X')

_,,_ : ∀ {n : Level} {@0 Δ : Tel} {X : Spine Δ → Set n} →
       (δ : Spine Δ) → X δ → Spine (Δ ** X)
· ,, x = x , ·
(a , δ) ,, x = a , (δ ,, x)

data OpTerm {n : Level} (T : Tel {n}) : Set (lsuc n) where
  ιᵀ : Spine T → OpTerm T

data Op {n : Level} (I : Tel {n}) (O : Tel {n}) : Set (lsuc n) where
  ι' : OpTerm O → Op I O
  _→ⁱ_ : OpTerm I → Op I O → Op I O
  _→ᵉ_ : (A : Set n) → (A → Op I O) → Op I O

ι : ∀ {n : Level} {I : Tel {n}} {O : Tel} → Spine O → Op I O
ι δ = ι' (ιᵀ δ)

liftᵉ : ∀ {n : Level} {I : Tel {n}} {O : Tel} {A : Set n} → (A → Op I O) → Op I O
liftᵉ {A = A} lam = A →ᵉ lam

data Sig {n : Level} (I : Tel {n}) (O : Tel) : Set (lsuc n) where
  ϵ : Sig I O
  _◃_ : Op I O → Sig I O → Sig I O

