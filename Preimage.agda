------------------------------------------------------------------------
-- Preimages
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on univalent foundations.

module Preimage where

open import Prelude
open import Path
open import Path.Lemmas
open import Path.Sum
open import Surjection hiding (id; _∘_)
open import Bijection hiding (id; _∘_)

-- The preimage of y under f is denoted by f ⁻¹ y.

infix 5 _⁻¹_

_⁻¹_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Set (a ⊔ b)
f ⁻¹ y = ∃ λ x → f x ≡ y

-- This is subject to changes
id⁻¹-contractible : ∀ {ℓ} {A : Set ℓ} (x : A) → Contractible (id ⁻¹ x)
id⁻¹-contractible x =
  ((x , refl x) ,
    λ {(x′ , x′≡x) →
        Σ≡⇒≡Σ (λ x′ → x′ ≡ x) (
          sym x′≡x ,
          elim″ (λ {x″} p → subst (λ x′ → x′ ≡ x) (sym p) (refl x) ≡ p) (refl _) x′≡x
        )})

postulate
  bijection⁻¹-contractible :
    ∀ {a b} {A : Set a} {B : Set b} (A↔B : A ↔ B) →
    let open _↔_ A↔B in ∀ y → Contractible (to ⁻¹ y)
