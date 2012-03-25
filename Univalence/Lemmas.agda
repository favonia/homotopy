------------------------------------------------------------------------
-- More lemmas
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

open import Univalence

module Univalence.Lemmas
  (univ : ∀ {ℓ} (A B : Set ℓ) → Univalence-axiom A B) where

open import Prelude
open import Path
open import Path.Lemmas
open import Map.Bijection hiding (_∘_; id)
open import Map.Weak-equivalence as Weak hiding (_∘_; id)

------------------------------------------------------------------------
-- Conversions between bijections, weak equivalences, and identities

≡≈≈ : ∀ {ℓ} (A B : Set ℓ) → (A ≡ B) ≈ (A ≈ B)
≡≈≈ A B = weq ≡⇒≈ (univ A B)

≈⇒≡ : ∀ {ℓ} {A B : Set ℓ} → A ≈ B → A ≡ B
≈⇒≡ = _≈_.from (≡≈≈ _ _)

subst-id-univ : ∀ {ℓ} {A B : Set ℓ} (A≡B : A ≡ B) (x : A) → subst id A≡B x ≡ _≈_.to (≡⇒≈ A≡B) x 
subst-id-univ {ℓ} =
  elim
    (λ {A B : Set ℓ} (A≡B : A ≡ B) → (x : A) → subst id A≡B x ≡ _≈_.to (≡⇒≈ A≡B) x)
    (λ A x → 
       subst id (refl A) x          ≡⟨ refl _ ⟩
       x                            ≡⟨ refl x ⟩
       (_≈_.to Weak.id) x           ≡⟨ refl _ ⟩∎
       (_≈_.to (≡⇒≈ (refl A))) x    ∎)

postulate
  ext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Extensionality A B

postulate
  ext-comp : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f g : A → B}
             (reason : ∀ x → f x ≡ g x) →
             ∀ x → cong (λ f → f x) (ext reason) ≡ reason x

postulate
  ext[dep] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → Extensionality[dep] A B

postulate
  ext-comp[dep] : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} {f g : (x : A) → B x}
             (reason : ∀ x → f x ≡ g x) →
             ∀ x → cong (λ f → f x) (ext[dep] reason) ≡ reason x
