------------------------------------------------------------------------
-- The univalence axiom
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia
-- Copyright (c) 2011-2012 Nils Anders Danielsson

{-# OPTIONS --without-K #-}

-- Partly based on Voevodsky's work on univalent foundations.

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

------------------------------------------------------------------------
-- Experimental Area
--
-- Another insight given by Robert Harper: UA is equivalence induction!
--
-- Here for some reasons I say "UA is weak-equivalence induction" insteaed.
-- (No good reasons for doing so, except that I want to reuse ≡⇒≈.)

private

  ≈-Elim : ∀ (ℓ₁ ℓ₂ : Level) → Set (lsuc (ℓ₁ ⊔ ℓ₂))
  ≈-Elim ℓ₁ ℓ₂ = ∀ (P : {A B : Set ℓ₁} → A ≈ B → Set ℓ₂) → ((A : Set ℓ₁) → P (Weak.id {A = A})) → ∀ {A B : Set ℓ₁} (A≈B : A ≈ B) → P A≈B
  
  ≈-Elim-refl : ∀ (ℓ₁ ℓ₂ : Level) → ≈-Elim ℓ₁ ℓ₂ → Set (lsuc (ℓ₁ ⊔ ℓ₂))
  ≈-Elim-refl ℓ₁ ℓ₂ ≈-elim = ∀ (P : {A B : Set ℓ₁} → A ≈ B → Set ℓ₂) → (pid : (A : Set ℓ₁) → P (Weak.id {A = A})) →
                             ∀ {A} → ≈-elim P pid Weak.id ≡ pid A
  
  weq-elim⇒univ : ∀ {ℓ}
    (≈-elim : ≈-Elim ℓ (lsuc ℓ)) →
    ≈-Elim-refl ℓ (lsuc ℓ) ≈-elim →
    (≈-elim′ : ≈-Elim ℓ ℓ) →
    ∀ {A B : Set ℓ} → Univalence-axiom A B
  weq-elim⇒univ {ℓ} ≈-elim ≈-elim-refl ≈-elim′ {A} {B} =
    _≈_.is-weak-equivalence $ ↔⇒≈ $ record
      { surjection = record
        { equivalence = record
          { to = ≡⇒≈
          ; from = ≈⇒≡
          }
        ; right-inverse-of = right-inverse-of
        }
      ; left-inverse-of = left-inverse-of
      }
      where  
        ≈⇒≡ : ∀ {A B : Set ℓ} → A ≈ B → A ≡ B
        ≈⇒≡ {A} {B} A≈B = ≈-elim (λ {A} {B} A≈B → A ≡ B) (λ A → refl A) A≈B
    
        ≈⇒≡-refl : ∀ (A : Set ℓ) → ≈⇒≡ (Weak.id {A = A}) ≡ refl A
        ≈⇒≡-refl A = ≈-elim-refl (λ {A} {B} A≈B → A ≡ B) (λ A → refl A)
    
        left-inverse-of : ∀ (A≡B : A ≡ B) → ≈⇒≡ (≡⇒≈ A≡B) ≡ A≡B
        left-inverse-of A≡B = elim
          (λ {A B} A≡B → ≈⇒≡ (≡⇒≈ A≡B) ≡ A≡B)
          (λ A → ≈⇒≡-refl A)
          A≡B
        
        right-inverse-of : ∀ (A≈B : A ≈ B) → ≡⇒≈ (≈⇒≡ A≈B) ≡ A≈B
        right-inverse-of A≈B = ≈-elim′
          (λ {A B : Set ℓ} A≈B → ≡⇒≈ (≈⇒≡ A≈B) ≡ A≈B)
          (λ A → cong ≡⇒≈ (≈⇒≡-refl A))
          A≈B
