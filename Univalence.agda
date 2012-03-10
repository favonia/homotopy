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
open import Path.Lemmas
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
-- Another insight given by Robert Harper:
--   The Univalence axiom is equivalence induction!
--
-- Note: Here we show that "weak-equivalent induction"
--   and the Univalence axiom is mutually derivable.

private

  -- The definition of "weak-equivalence induction"
  ≈-Elim : ∀ (ℓ₁ ℓ₂ : Level) → Set (lsuc (ℓ₁ ⊔ ℓ₂))
  ≈-Elim ℓ₁ ℓ₂ = ∀ (P : {A B : Set ℓ₁} → A ≈ B → Set ℓ₂) →
                 ((A : Set ℓ₁) → P (Weak.id {A = A})) →
                 ∀ {A B : Set ℓ₁} (A≈B : A ≈ B) → P A≈B
  
  ≈-Elim-id : ∀ (ℓ₁ ℓ₂ : Level) → ≈-Elim ℓ₁ ℓ₂ → Set (lsuc (ℓ₁ ⊔ ℓ₂))
  ≈-Elim-id ℓ₁ ℓ₂ ≈-elim = ∀ (P : {A B : Set ℓ₁} → A ≈ B → Set ℓ₂) →
                           (pid : (A : Set ℓ₁) → P (Weak.id {A = A})) →
                           ∀ {A} → ≈-elim P pid Weak.id ≡ pid A

  -- The elimination rule for weak equivalence implies UA
  weq-elim⇒univ : ∀ {ℓ}
    (≈-elim : ≈-Elim ℓ (lsuc ℓ)) →
    ≈-Elim-id ℓ (lsuc ℓ) ≈-elim →
    (≈-elim′ : ≈-Elim ℓ ℓ) →
    ∀ (A B : Set ℓ) → Univalence-axiom A B
  weq-elim⇒univ {ℓ} ≈-elim ≈-elim-id ≈-elim′ A B =
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
        ≈⇒≡-refl A = ≈-elim-id (λ {A} {B} A≈B → A ≡ B) (λ A → refl A)
    
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

  -- The other way around.
  --
  -- (Maybe we should have one big lemma outputting a tuple (Σ type) directly?)
  -- TODO Find a cleaner proof
  univ⇒weq-elim : ∀ {ℓ ℓ′} → (∀ (A B : Set ℓ) → Univalence-axiom A B) → ≈-Elim ℓ ℓ′
  univ⇒weq-elim {ℓ} {ℓ′} univ P pid {A} {B} A≈B =
      subst P right-inverse (elim (λ {A B : Set ℓ} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ A≈B))
      where
        A≡B≈A≈B : (A ≡ B) ≈ (A ≈ B)
        A≡B≈A≈B = weq ≡⇒≈ (univ A B)

        ≈⇒≡ : A ≡ B → A ≈ B
        ≈⇒≡ = _≈_.from A≡B≈A≈B

        right-inverse : ≡⇒≈ (≈⇒≡ A≈B) ≡ A≈B
        right-inverse = _≈_.right-inverse-of A≡B≈A≈B A≈B

  univ⇒weq-elim-id : ∀ {ℓ ℓ′} → (univ : ∀ (A B : Set ℓ) → Univalence-axiom A B) →
                     ≈-Elim-id ℓ ℓ′ (univ⇒weq-elim univ)
  univ⇒weq-elim-id {ℓ} {ℓ′} univ P pid {A} =
      subst P right-inverse (elim (λ {A B : Set ℓ} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ Weak.id))
          ≡⟨ refl _ ⟩
      subst P right-inverse (elim (λ {A B : Set ℓ} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ Weak.id))
          ≡⟨ cong (subst P right-inverse) $ sym $ cong[dep] (P ∘ ≡⇒≈) (elim (λ {A B : Set ℓ} A≡B → P (≡⇒≈ A≡B)) pid) $ sym $ left-inverse ⟩
      subst P right-inverse (subst (P ∘ ≡⇒≈) (sym left-inverse) (elim (λ {A B : Set ℓ} A≡B → P (≡⇒≈ A≡B)) pid (refl A)))
          ≡⟨ refl _ ⟩
      subst P right-inverse (subst (P ∘ ≡⇒≈) (sym left-inverse) (pid A))
          ≡⟨ cong (subst P right-inverse) $ sym $ subst-cong P ≡⇒≈ (sym left-inverse) (pid A) ⟩
      subst P right-inverse (subst P (cong ≡⇒≈ (sym left-inverse)) (pid A))
          ≡⟨ cong (λ p → subst P right-inverse (subst P p (pid A))) $ cong-sym ≡⇒≈ left-inverse ⟩
      subst P right-inverse (subst P (sym (cong ≡⇒≈ left-inverse)) (pid A))
          ≡⟨ cong (λ p → subst P right-inverse (subst P (sym p) (pid A))) $ cong-left ⟩
      subst P right-inverse (subst P (sym right-inverse) (pid A))
          ≡⟨ sym $ subst-trans P (sym right-inverse) right-inverse (pid A) ⟩
      subst P (trans (sym right-inverse) right-inverse) (pid A)
          ≡⟨ cong (λ p → subst P p (pid A)) $ trans-symˡ right-inverse ⟩∎
      pid A
          ∎
      where
        A≡A≈A≈A : (A ≡ A) ≈ (A ≈ A)
        A≡A≈A≈A = weq ≡⇒≈ (univ A A)

        ≈⇒≡ : A ≡ A → A ≈ A
        ≈⇒≡ = _≈_.from A≡A≈A≈A

        left-inverse : ≈⇒≡ Weak.id ≡ refl A
        left-inverse = _≈_.left-inverse-of A≡A≈A≈A (refl A)

        right-inverse : ≡⇒≈ (≈⇒≡ Weak.id) ≡ Weak.id
        right-inverse = _≈_.right-inverse-of A≡A≈A≈A Weak.id

        cong-left : cong ≡⇒≈ left-inverse ≡ right-inverse
        cong-left = _≈_.left-right-lemma A≡A≈A≈A (refl A)
