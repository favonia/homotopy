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
open import Map.WeakEquivalence as Weak hiding (_∘_; id)

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
--   and the Univalence axiom are mutually derivable.

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

  -- The elimination and computation rules imply Univalence
  weq-elim⇒univ : ∀ {ℓ} (≈-elim : ≈-Elim ℓ (lsuc ℓ)) → ≈-Elim-id ℓ (lsuc ℓ) ≈-elim →
                  ∀ (A B : Set ℓ) → Univalence-axiom A B
  weq-elim⇒univ {ℓ} ≈-elim ≈-elim-id A B =
    _≈_.is-weak-equivalence $ ↔⇒≈ $ record
      { surjection = record
        { to               = ≡⇒≈
        ; from             = ≈⇒≡
        ; right-inverse-of = right-inverse-of
        }
      ; left-inverse-of = left-inverse-of
      }
      where  
        ≈⇒≡ : ∀ {A B : Set ℓ} → A ≈ B → A ≡ B
        ≈⇒≡ = ≈-elim (λ {A} {B} A≈B → A ≡ B) (λ A → refl A)
    
        ≈⇒≡-id : ∀ (A : Set ℓ) → ≈⇒≡ Weak.id ≡ refl A
        ≈⇒≡-id A = ≈-elim-id (λ {A B} A≈B → A ≡ B) (λ A → refl A)
    
        left-inverse-of : ∀ (A≡B : A ≡ B) → ≈⇒≡ (≡⇒≈ A≡B) ≡ A≡B
        left-inverse-of A≡B = elim
          (λ {A B} A≡B → ≈⇒≡ (≡⇒≈ A≡B) ≡ A≡B)
          (λ A → ≈⇒≡-id A)
          A≡B
       
        -- Here we use ↑ to handle the universe mismatch.
        right-inverse-of : ∀ (A≈B : A ≈ B) → ≡⇒≈ (≈⇒≡ A≈B) ≡ A≈B
        right-inverse-of A≈B = ↑.lower $ ≈-elim
          (λ {A B : Set ℓ} A≈B → ↑ (lsuc ℓ) (≡⇒≈ (≈⇒≡ A≈B) ≡ A≈B))
          (λ A → lift (cong ≡⇒≈ (≈⇒≡-id A)))
          A≈B

  -- The other way around. The Univalence axiom implies both.
  --
  -- Maybe we should have one big lemma outputting a pair containing
  -- the elimination rule and the computation rule directly?
  univ⇒weq-elim : ∀ {ℓ ℓ′} → (∀ (A B : Set ℓ) → Univalence-axiom A B) → ≈-Elim ℓ ℓ′
  univ⇒weq-elim {ℓ} {ℓ′} univ P pid {A} {B} A≈B =
      subst P right-inverse (elim (λ {A B : Set ℓ} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ A≈B))
      where
        A≡B≈A≈B : (A ≡ B) ≈ (A ≈ B)
        A≡B≈A≈B = weq ≡⇒≈ (univ A B)

        ≈⇒≡ : A ≈ B → A ≡ B
        ≈⇒≡ = _≈_.from A≡B≈A≈B

        right-inverse : ≡⇒≈ (≈⇒≡ A≈B) ≡ A≈B
        right-inverse = _≈_.right-inverse-of A≡B≈A≈B A≈B

  univ⇒weq-elim-id : ∀ {ℓ ℓ′} (univ : ∀ (A B : Set ℓ) → Univalence-axiom A B) →
                     ≈-Elim-id ℓ ℓ′ (univ⇒weq-elim univ)
  univ⇒weq-elim-id {ℓ} {ℓ′} univ P pid {A} =
      subst P right-inverse (elim (λ {_ _} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ Weak.id))
          ≡⟨ cong (λ p → subst P p (elim (λ {_ _} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ Weak.id))) $ sym cong-left ⟩
      subst P (cong ≡⇒≈ left-inverse) (elim (λ {_ _} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ Weak.id))
          ≡⟨ subst-cong P ≡⇒≈ left-inverse (elim (λ {_ _} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ Weak.id)) ⟩
      subst (P ∘ ≡⇒≈) left-inverse (elim (λ {_ _} A≡B → P (≡⇒≈ A≡B)) pid (≈⇒≡ Weak.id))
          ≡⟨ cong[dep] (P ∘ ≡⇒≈) (elim (λ {_ _} A≡B → P (≡⇒≈ A≡B)) pid) left-inverse ⟩∎
      elim (λ {_ _} A≡B → P (≡⇒≈ A≡B)) pid (refl A)
          ∎
      where
        A≡A≈A≈A : (A ≡ A) ≈ (A ≈ A)
        A≡A≈A≈A = weq ≡⇒≈ (univ A A)

        ≈⇒≡ : A ≈ A → A ≡ A
        ≈⇒≡ = _≈_.from A≡A≈A≈A

        left-inverse : ≈⇒≡ Weak.id ≡ refl A
        left-inverse = _≈_.left-inverse-of A≡A≈A≈A (refl A)

        right-inverse : ≡⇒≈ (≈⇒≡ Weak.id) ≡ Weak.id
        right-inverse = _≈_.right-inverse-of A≡A≈A≈A Weak.id

        cong-left : cong ≡⇒≈ left-inverse ≡ right-inverse
        cong-left = _≈_.left-right-lemma A≡A≈A≈A (refl A)
