------------------------------------------------------------------------
-- Paths in flowers
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

open import Univalence

module Space.Flower.Omega1
  (univ : ∀ {ℓ} (A B : Set ℓ) → Univalence-axiom A B) where

open import Prelude renaming (_∘_ to _⊙_)
open import Path
open import Path.Lemmas
open import Path.Sum
open import Path.HigherOrder
open import Map.H-equivalence hiding (_∘_; id)
open import Map.WeakEquivalence as Weak hiding (_∘_; id)

import Univalence.Lemmas; open Univalence.Lemmas univ

import Space.FreeGroup; open Space.FreeGroup univ
open import Space.Flower

------------------------------------------------------------------------
-- From free groups to loops

private
  word⇒petal : ∀ {n} → Word n → core n ≡ core n
  word⇒petal [] = refl _
  word⇒petal (gen i ∷ xs) = trans (word⇒petal xs) (petal i)
  word⇒petal (inv i ∷ xs) = trans (word⇒petal xs) (sym $ petal i)

free-group⇒petal : ∀ {n} → FreeGroup n → core n ≡ core n
free-group⇒petal (xs , n) = word⇒petal xs

------------------------------------------------------------------------
-- From loops to free groups

private
  cons-gen : ∀ {n} (i : Fin n) → FreeGroup n → FreeGroup n
  cons-gen i = cons (gen i)
  
  cons-inv : ∀ {n} (i : Fin n) → FreeGroup n → FreeGroup n
  cons-inv i = cons (inv i)

  cons-gen-inv : ∀ {n} i (f : FreeGroup n) → cons-gen i (cons-inv i f) ≡ f
  cons-gen-inv i = cons₂-flipʳ (gen i)
  
  cons-inv-gen : ∀ {n} i (f : FreeGroup n) → cons-inv i (cons-gen i f) ≡ f
  cons-inv-gen i = cons₂-flipʳ (inv i)

  -- The non-trivial homotopies equivalence between the free group
  cons-gen-↔ : ∀ {n} → Fin n → FreeGroup n ↔ FreeGroup n
  cons-gen-↔ i = record
    { surjection = record
      { to = cons-gen i
      ; from = cons-inv i
      ; right-inverse-of = cons-gen-inv i
      }
    ; left-inverse-of = cons-inv-gen i
    }

  cons-gen-≈ : ∀ {n} → Fin n → FreeGroup n ≈ FreeGroup n
  cons-gen-≈ = ↔⇒≈ ⊙ cons-gen-↔

  cons-gen-≡ : ∀ {n} → Fin n → FreeGroup n ≡ FreeGroup n
  cons-gen-≡ = ≈⇒≡ ⊙ cons-gen-≈

  -- The standard trick to build a universal covering
  C : ∀ {n} → Flower n → Set
  C {n} = Flower-elim[simp] (FreeGroup n) cons-gen-≡

  abstract
    subst-C-petal : ∀ {n} i (f : FreeGroup n) → subst C (petal i) f ≡ cons-gen i f
    subst-C-petal {n} i f =
      subst C (petal i) f
        ≡⟨ sym $ subst-cong id C (petal i) f ⟩
      subst id (cong C (petal i)) f
        ≡⟨ cong (λ p → subst id p f) $ Flower-elim[simp]-petal (FreeGroup n) cons-gen-≡ i ⟩
      subst id (cons-gen-≡ i) f
        ≡⟨ subst-id-univ (cons-gen-≡ i) f ⟩
      _≈_.to (≡⇒≈ $ cons-gen-≡ i) f
        ≡⟨ cong (λ weq → _≈_.to weq f) $ right-inverse-of $ cons-gen-≈ i ⟩∎
      cons-gen i f
        ∎
      where
        open _≈_ (≡≈≈ (FreeGroup n) (FreeGroup n))

  subst-C-petal-cons-inv : ∀ {n} i (f : FreeGroup n) → subst C (petal i) (cons-inv i f) ≡ f
  subst-C-petal-cons-inv {n} i f =
    subst C (petal i) (cons-inv i f)
      ≡⟨ subst-C-petal i (cons-inv i f) ⟩
    cons-gen i (cons-inv i f)
      ≡⟨ cons-gen-inv i f ⟩∎
    f
      ∎

  subst-C-sym-petal : ∀ {n} i (f : FreeGroup n) → subst C (sym $ petal i) f ≡ cons-inv i f
  subst-C-sym-petal i f = subst-sym C (petal i) f (cons-inv i f) $ subst-C-petal-cons-inv i f

-- The counting function
petal⇒free-group : ∀ {n} → core n ≡ core n → FreeGroup n
petal⇒free-group p = subst C p unit

------------------------------------------------------------------------
-- Homotopy equivalence

private
  private
    -- The right inverse
    right-inverse-of′ : ∀ {n} (xs : Word n) → Normalized xs →
                        proj₁ (petal⇒free-group (word⇒petal xs)) ≡ xs
    right-inverse-of′ []           ∅ = refl _
    right-inverse-of′ (gen i ∷ []) ✭ =
      proj₁ (subst C (petal i) unit)
        ≡⟨ cong proj₁ $ subst-C-petal i unit ⟩∎
      gen i ∷ []
        ∎
    right-inverse-of′ (inv i ∷ []) ✭ =
      proj₁ (subst C (sym $ petal i) unit)
        ≡⟨ cong proj₁ $ subst-C-sym-petal i unit ⟩∎
      inv i ∷ []
        ∎
    right-inverse-of′ (gen i ∷ x ∷ xs) (s ▸ n) =
      proj₁ (subst C (trans (word⇒petal $ x ∷ xs) (petal i)) unit)
        ≡⟨ cong proj₁ $ subst-trans C (word⇒petal $ x ∷ xs) (petal i) unit ⟩
      proj₁ (subst C (petal i) $ subst C (word⇒petal $ x ∷ xs) unit)
        ≡⟨ cong (proj₁ ⊙ subst C (petal i)) $ word-≡⇒free-group-≡ $ right-inverse-of′ (x ∷ xs) n ⟩
      proj₁ (subst C (petal i) (x ∷ xs , n))
        ≡⟨ cong proj₁ $ subst-C-petal i (x ∷ xs , n) ⟩
      proj₁ (cons-gen i (x ∷ xs , n))
        ≡⟨ cong proj₁ $ cons-stable s n ⟩∎
      gen i ∷ x ∷ xs
        ∎
    right-inverse-of′ (inv i ∷ x ∷ xs) (s ▸ n) =
      proj₁ (subst C (trans (word⇒petal $ x ∷ xs) (sym $ petal i)) unit)
        ≡⟨ cong proj₁ $ subst-trans C (word⇒petal $ x ∷ xs) (sym $ petal i) unit ⟩
      proj₁ (subst C (sym $ petal i) $ subst C (word⇒petal $ x ∷ xs) unit)
        ≡⟨ cong (proj₁ ⊙ subst C (sym $ petal i)) $ word-≡⇒free-group-≡ $ right-inverse-of′ (x ∷ xs) n ⟩
      proj₁ (subst C (sym $ petal i) (x ∷ xs , n))
        ≡⟨ cong proj₁ $ subst-C-sym-petal i (x ∷ xs , n) ⟩
      proj₁ (cons-inv i (x ∷ xs , n))
        ≡⟨ cong proj₁ $ cons-stable s n ⟩∎
      inv i ∷ x ∷ xs
        ∎

  right-inverse-of : ∀ {n} (f : FreeGroup n) → petal⇒free-group (free-group⇒petal f) ≡ f
  right-inverse-of (xs , n) = word-≡⇒free-group-≡ $ right-inverse-of′ xs n

  -- Intuition:
  --
  -- J rule works on paths, not loops...
  -- Let's free one of the end points!

  free-group⇒petal-cons-inv : ∀ {n} i (f : FreeGroup n) →
                                free-group⇒petal (cons-inv i f) ≡ trans (free-group⇒petal f) (sym $ petal i)
  free-group⇒petal-cons-inv i ([]     , ∅) = refl _
  free-group⇒petal-cons-inv i (x ∷ xs , n) with decideStable (inv i) x
  ... | inj₁ _  = refl _
  ... | inj₂ ¬s =
    word⇒petal xs
      ≡⟨ sym $ trans-trans-symʳʳ (word⇒petal xs) (petal i) ⟩
    trans (word⇒petal (gen i ∷ xs)) (sym $ petal i)
      ≡⟨ cong (λ x → trans (word⇒petal (x ∷ xs)) (sym $ petal i)) $ sym $ ¬stable⇒flip ¬s ⟩∎
    trans (word⇒petal (x ∷ xs)) (sym $ petal i)
      ∎

  -- Data to be fed into Flower-elim
  free-group⇒petal-petal : ∀ {n} i (f : FreeGroup n) →
                             subst (λ x → C x → core n ≡ x) (petal i) free-group⇒petal f ≡ free-group⇒petal f
  free-group⇒petal-petal {n} i f = 
    subst (λ x → C x → core n ≡ x) (petal i) free-group⇒petal f 
      ≡⟨ subst-func C (λ x → core n ≡ x) (petal i) free-group⇒petal (subst-C-petal-cons-inv i f) ⟩
    subst (λ x → core n ≡ x) (petal i) (free-group⇒petal $ cons-inv i f)
      ≡⟨ subst-path[idʳ] (const $ core n) (petal i) (free-group⇒petal $ cons-inv i f) ⟩
    trans (sym $ cong (const $ core n) $ petal i) (trans (free-group⇒petal $ cons-inv i f) $ petal i)
      ≡⟨ cong (λ p → trans (sym p) (trans (free-group⇒petal $ cons-inv i f) $ petal i)) $ cong-const (core n) (petal i) ⟩
    trans (free-group⇒petal $ cons-inv i f) (petal i)
      ≡⟨ cong (λ p → trans p (petal i)) $ free-group⇒petal-cons-inv i f ⟩
    trans (trans (free-group⇒petal f) (sym $ petal i)) (petal i)
      ≡⟨ trans-trans-symʳ (free-group⇒petal f) (petal i) ⟩∎
    free-group⇒petal f
      ∎

  -- A generalized Cx⇒petal ... Cx⇒fractal !
  Cx⇒fractal : ∀ {n} (x : Flower n) → C x → core n ≡ x
  Cx⇒fractal {n} = Flower-elim (λ x → C x → core n ≡ x) free-group⇒petal (ext ⊙ free-group⇒petal-petal)

  -- A generalized S¹loop⇒Cx ... S¹path⇒Cx !
  fractal⇒Cx : ∀ {n} (x : Flower n) → core n ≡ x → C x
  fractal⇒Cx x p = subst C p unit

  -- The generalized left inversion property (now easy?)
  left-inverse-of′ : ∀ {n} (x : Flower n) → (p : core n ≡ x) → Cx⇒fractal x (fractal⇒Cx x p) ≡ p
  left-inverse-of′ x = elim′ (λ {x} p → Cx⇒fractal x (fractal⇒Cx x p) ≡ p) (refl _)

  -- The left inversion property we want
  left-inverse-of : ∀ {n} → (p : core n ≡ core n) → free-group⇒petal (petal⇒free-group p) ≡ p
  left-inverse-of {n} = left-inverse-of′ $ core n

-- We have all the ingredients now!
Ω₁-flower↔free-group : ∀ n → Ω 1 (core n) ↔ FreeGroup n
Ω₁-flower↔free-group n =
  record
  { surjection = record
    { to = petal⇒free-group
    ; from = free-group⇒petal
    ; right-inverse-of = right-inverse-of
    }
  ; left-inverse-of = left-inverse-of
  }
