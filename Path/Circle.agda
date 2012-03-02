------------------------------------------------------------------------
-- Paths in circles
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- Credits:
--   * As far as I know, Peter Lumsdaine gave the construction.
--   * I followed Danial Licata's presentation.

open import Univalence

module Path.Circle
  (univ : ∀ {ℓ} (A B : Set ℓ) → Univalence-axiom A B) where

open import Prelude renaming (zero to ℕzero; suc to ℕsuc)
open import Path
open import Path.Lemmas
open import Path.Sum
open import Bijection hiding (_∘_; id)
open import Weak-equivalence as Weak hiding (_∘_; id)

import Univalence.Lemmas; open Univalence.Lemmas univ
import Univalence.Extensionality; open Univalence.Extensionality univ

open import Inductive.Integer
open import HigherInductive.Sphere

------------------------------------------------------------------------
-- From ℤ to paths

private
  repeat : ℕ → base ≡ base → base ≡ base
  repeat ℕzero _ = refl base
  repeat (ℕsuc n) loop = trans (repeat n loop) loop

ℤ⇒S¹loop : ℤ → base ≡ base
ℤ⇒S¹loop zero = refl base
ℤ⇒S¹loop (pos n) = repeat (ℕsuc n) loop
ℤ⇒S¹loop (neg n) = repeat (ℕsuc n) (sym loop)

------------------------------------------------------------------------
-- From paths to ℤ

private
  suc : ℤ → ℤ
  suc zero = pos ℕzero
  suc (pos i) = pos (ℕsuc i)
  suc (neg ℕzero) = zero
  suc (neg (ℕsuc i)) = neg i

  pred : ℤ → ℤ
  pred zero = neg ℕzero
  pred (neg i) =  neg (ℕsuc i)
  pred (pos ℕzero) = zero
  pred (pos (ℕsuc i)) = pos i

  suc-pred : ∀ (i : ℤ) → suc (pred i) ≡ i
  suc-pred zero = refl _
  suc-pred (neg i) = refl _
  suc-pred (pos ℕzero) = refl _
  suc-pred (pos (ℕsuc i)) = refl _

  pred-suc : ∀ (i : ℤ) → pred (suc i) ≡ i
  pred-suc zero = refl _
  pred-suc (pos i) = refl _
  pred-suc (neg ℕzero) = refl _
  pred-suc (neg (ℕsuc i)) = refl _

  -- The non-trivial bijection between ℤ
  suc-↔ : ℤ ↔ ℤ
  suc-↔ = record
    { surjection = record
      { equivalence = record
        { to = suc
        ; from = pred
        }
      ; right-inverse-of = suc-pred
      }
    ; left-inverse-of = pred-suc
    }

  suc-≈ : ℤ ≈ ℤ
  suc-≈ = ↔⇒≈ suc-↔

  suc-≡ : ℤ ≡ ℤ
  suc-≡ = ≈⇒≡ suc-≈

  -- The standard trick to build a universal covering
  C : S¹ → Set
  C = S¹-elim[simp] ℤ suc-≡

  abstract
    subst-C-loop : ∀ x → subst C loop x ≡ suc x
    subst-C-loop x =
      subst C loop x              ≡⟨ sym $ subst-id-cong C loop x ⟩
      subst id (cong C loop) x    ≡⟨ cong (λ p → subst id p x) $ cong-S¹-elim[simp]-loop ℤ suc-≡ ⟩
      subst id suc-≡ x            ≡⟨ subst-id-univ suc-≡ x ⟩
      _≈_.to (≡⇒≈ suc-≡) x        ≡⟨ cong (λ weq → _≈_.to weq x) $ right-inverse-of suc-≈ ⟩
      _≈_.to suc-≈ x              ≡⟨ refl (suc x) ⟩∎
      suc x                       ∎
      where
        open _≈_ (≡≈≈ ℤ ℤ)

  subst-C-loop-pred : ∀ x → subst C loop (pred x) ≡ x
  subst-C-loop-pred x =
    subst C loop (pred x)       ≡⟨ subst-C-loop (pred x) ⟩
    suc (pred x)                ≡⟨ suc-pred x ⟩∎
    x                           ∎

  subst-C-sym-loop : ∀ x → subst C (sym loop) x ≡ pred x
  subst-C-sym-loop x = subst-sym C loop x (pred x) $ subst-C-loop-pred x

-- The counting function
S¹loop⇒ℤ : base ≡ base → ℤ
S¹loop⇒ℤ p = subst C p zero

------------------------------------------------------------------------
-- Bijection

private
  -- The right inverse (easy)
  right-inverse-of : ∀ z → S¹loop⇒ℤ (ℤ⇒S¹loop z) ≡ z
  right-inverse-of zero = refl _
  right-inverse-of (pos n) = right-inverse-of-pos n
    where
      right-inverse-of-pos : ∀ n → S¹loop⇒ℤ (ℤ⇒S¹loop (pos n)) ≡ pos n
      right-inverse-of-pos ℕzero = 
          subst C (trans (refl base) loop) zero     ≡⟨ refl _ ⟩
          subst C loop zero                         ≡⟨ subst-C-loop zero ⟩∎
          pos ℕzero                                 ∎
      right-inverse-of-pos (ℕsuc n) = 
          subst C (trans (repeat (ℕsuc n) loop) loop) zero    ≡⟨ subst-trans C (repeat (ℕsuc n) loop) loop zero ⟩
          subst C loop (subst C (repeat (ℕsuc n) loop) zero)  ≡⟨ cong (subst C loop) $ right-inverse-of-pos n ⟩
          subst C loop (pos n)                                ≡⟨ subst-C-loop (pos n) ⟩∎
          pos (ℕsuc n)                                        ∎
  right-inverse-of (neg n) = right-inverse-of-neg n
    where
      right-inverse-of-neg : ∀ n → S¹loop⇒ℤ (ℤ⇒S¹loop (neg n)) ≡ neg n
      right-inverse-of-neg ℕzero = 
          subst C (trans (refl base) (sym loop)) zero     ≡⟨ refl _ ⟩
          subst C (sym loop) zero                         ≡⟨ subst-C-sym-loop zero ⟩∎
          neg ℕzero                                       ∎
      right-inverse-of-neg (ℕsuc n) = 
          subst C (trans (repeat (ℕsuc n) (sym loop)) (sym loop)) zero   ≡⟨ subst-trans C (repeat (ℕsuc n) (sym loop)) (sym loop) zero ⟩
          subst C (sym loop) (subst C (repeat (ℕsuc n) (sym loop)) zero) ≡⟨ cong (subst C (sym loop)) $ right-inverse-of-neg n ⟩
          subst C (sym loop) (neg n)                                      ≡⟨ subst-C-sym-loop (neg n) ⟩∎
          neg (ℕsuc n)                                                    ∎

  -- Intuition:
  --
  -- J rule works on paths, not loops...
  -- Let's free one of the end points!

  -- A trasporting loop to be fed into S¹-elim
  ℤ⇒S¹path-loop : ∀ z → subst (λ x → C x → base ≡ x) loop ℤ⇒S¹loop z ≡ ℤ⇒S¹loop z
  ℤ⇒S¹path-loop z = 
    subst (λ x → C x → base ≡ x) loop ℤ⇒S¹loop z
        ≡⟨ sym $ subst-app C (λ x → base ≡ x) loop ℤ⇒S¹loop (subst-C-loop-pred z) ⟩
    subst (λ x → base ≡ x) loop (ℤ⇒S¹loop (pred z))
        ≡⟨ subst-path[id] (const base) loop (ℤ⇒S¹loop (pred z)) ⟩
    trans (sym (cong (const base) loop)) (trans (ℤ⇒S¹loop (pred z)) loop)
        ≡⟨ cong (λ p → trans (sym p) (trans (ℤ⇒S¹loop (pred z)) loop)) $ cong-const base loop ⟩
    trans (ℤ⇒S¹loop (pred z)) loop
        ≡⟨ lemma z ⟩∎
    ℤ⇒S¹loop z
        ∎
    where
      lemma : ∀ z → trans (ℤ⇒S¹loop (pred z)) loop ≡ ℤ⇒S¹loop z
      lemma zero = trans-symˡ loop
      lemma (pos ℕzero) = refl _
      lemma (pos (ℕsuc n)) = refl _
      lemma (neg _) = trans-trans-symʳ _ _

  -- A generalized ℤ⇒S¹loop ... ℤ⇒S¹path !
  ℤ⇒S¹path : ∀ (x : S¹) → C x → base ≡ x
  ℤ⇒S¹path = S¹-elim (λ x → C x → base ≡ x) ℤ⇒S¹loop (ext ℤ⇒S¹path-loop)
  
  -- A generalized S¹loop⇒ℤ ... S¹path⇒ℤ !
  S¹path⇒ℤ : ∀ (x : S¹) → base ≡ x → C x
  S¹path⇒ℤ x p = subst C p zero

  -- The generalized left inversion property (now easy?)
  left-inverse-of′ : ∀ (x : S¹) → (p : base ≡ x) → ℤ⇒S¹path x (S¹path⇒ℤ x p) ≡ p
  left-inverse-of′ x = elim′ (λ {x} p → ℤ⇒S¹path x (S¹path⇒ℤ x p) ≡ p) (refl _)

  -- The left inversion property we want
  left-inverse-of : (p : base ≡ base) → ℤ⇒S¹loop (S¹loop⇒ℤ p) ≡ p
  left-inverse-of = left-inverse-of′ base

-- We have all the ingredients now!
S¹loop↔ℤ : base ≡ base ↔ ℤ
S¹loop↔ℤ =
  record
  { surjection = record
    { equivalence = record
      { to = S¹loop⇒ℤ
      ; from = ℤ⇒S¹loop
      }
    ; right-inverse-of = right-inverse-of
    }
  ; left-inverse-of = left-inverse-of
  }
