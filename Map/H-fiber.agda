------------------------------------------------------------------------
-- Homotopy Fibers
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on univalent foundations.

module Map.H-fiber where

open import Prelude
open import Path

open import Map.Surjection hiding (id; _∘_)
open import Map.H-equivalence hiding (id; _∘_)

-- The homotopy fiber of y under f is denoted by f ⁻¹ y.

infix 5 _⁻¹_

_⁻¹_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Set (a ⊔ b)
f ⁻¹ y = ∃ λ x → f x ≡ y

-- This is subject to changes
id⁻¹-contractible : ∀ {ℓ} {A : Set ℓ} (x : A) → Contractible (id ⁻¹ x)
id⁻¹-contractible y = (y , refl y) , λ {(_ , p) → elim″ (λ {x} p → (y , refl y) ≡ (x , p)) (refl _) p}

postulate
  hequiv⁻¹-contractible :
    ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (A↔B : A ↔ B) →
    let open _↔_ A↔B in ∀ y → Contractible (to ⁻¹ y)
{-
hequiv⁻¹-contractible A↔B y =
  (from y , right-inverse-of y) ,
  λ {(x , to-x≡y) → elim′ (λ {x} p → (from y , right-inverse-of y) ≡ (x , p)) (refl _) to-x≡y}
  where
    open _↔_ A↔B

    lemma : ∀ x → (from (to x) , right-inverse-of (to x)) ≡ (x , refl (to x))
-}
