------------------------------------------------------------------------
-- The univalence axiom
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

module Univalence where

open import Prelude
open import Path
open import Weak-equivalence as Weak hiding (_∘_; id)

------------------------------------------------------------------------
-- The univalence axiom

-- If two sets are equal, then they are weakly equivalent.

≡⇒≈ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≈ B
≡⇒≈ = elim (λ {A B} _ → A ≈ B) (λ _ → Weak.id)

-- The univalence axiom states that ≡⇒≈ is a weak equivalence.

Univalence-axiom : ∀ {ℓ} → Set ℓ → Set ℓ → Set (lsuc ℓ)
Univalence-axiom A B = Is-weak-equivalence (≡⇒≈ {A = A} {B = B})

