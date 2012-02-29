------------------------------------------------------------------------
-- Extensionality for functions
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on so-called univalent
-- foundations.

open import Univalence

module Univalence.Extensionality
  (univ : ∀ {ℓ} (A B : Set ℓ) → Univalence-axiom A B) where

open import Path
open import Path.Lemmas
open import Prelude
open import Weak-equivalence hiding (_∘_; id)

------------------------------------------------------------------------
-- Non-dependent extensionality for functions of a certain type.

Extensionality : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
Extensionality A B = {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

Extensionality[dep] : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
Extensionality[dep] A B = {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- A consequence: extensionality for functions

postulate
  ext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Extensionality A B

postulate
  ext-elim : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f g : A → B}
             (reason : ∀ x → f x ≡ g x) →
             ∀ x → cong (λ f → f x) (ext reason) ≡ reason x

postulate
  ext[dep] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → Extensionality[dep] A B

postulate
  ext-elim[dep] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x}
             (reason : ∀ x → f x ≡ g x) →
             ∀ x → cong (λ f → f x) (ext[dep] reason) ≡ reason x
