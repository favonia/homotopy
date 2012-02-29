------------------------------------------------------------------------
-- Preimages
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.


module Preimage where

open import Prelude
open import Path
open import Path.Lemmas
open import Surjection hiding (id; _∘_)
open import Bijection hiding (id; _∘_)

-- The preimage of y under f is denoted by f ⁻¹ y.

infix 5 _⁻¹_

_⁻¹_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Set (a ⊔ b)
f ⁻¹ y = ∃ λ x → f x ≡ y

postulate
  bijection⁻¹-contractible :
    ∀ {a b} {A : Set a} {B : Set b} (A↔B : A ↔ B) →
    let open _↔_ A↔B in ∀ y → Contractible (to ⁻¹ y)
