------------------------------------------------------------------------
-- Paths in circles
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- Credits:
--   * As far as I know, Peter Lumsdaine gave the idea.

open import Univalence

module Path.Circle
  (univ : ∀ {ℓ} (A B : Set ℓ) → Univalence-axiom A B) where

open import Prelude renaming (zero to ℕzero; suc to ℕsuc;
                              ℤzero to zero; ℤpos to pos; ℤneg to neg )
open import Path
open import Path.Lemmas
open import Path.Sum
open import Bijection hiding (_∘_; id)
open import Weak-equivalence as Weak hiding (_∘_; id)

import Univalence.Lemmas; open Univalence.Lemmas univ
import Univalence.Extensionality; open Univalence.Extensionality univ

open import HigherInductive.Sphere

------------------------------------------------------------------------
-- From ℤ to paths

private
  looping : ℕ → base ≡ base → base ≡ base
  looping ℕzero _ = refl base
  looping (ℕsuc n) loop = trans (looping n loop) loop

ℤ→S¹≡ : ℤ → base ≡ base
ℤ→S¹≡ zero = refl base
ℤ→S¹≡ (pos n) = looping (ℕsuc n) loop
ℤ→S¹≡ (neg n) = looping (ℕsuc n) (sym loop)

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

  -- Standard trick to count loops
  C : S¹ → Set
  C = S¹-rec[simp] ℤ suc-≡

  subst-C-loop : ∀ x → subst C loop x ≡ suc x
  subst-C-loop x =
    subst C loop x              ≡⟨ sym $ subst-id-cong C loop x ⟩
    subst id (cong C loop) x    ≡⟨ cong (λ p → subst id p x) $ cong-S¹-rec[simp]-loop ℤ suc-≡ ⟩
    subst id suc-≡ x            ≡⟨ subst-id-univ suc-≡ x ⟩
    _≈_.to (≡⇒≈ suc-≡) x        ≡⟨ cong (λ weq → _≈_.to weq x) $ right-inverse-of suc-≈ ⟩
    _≈_.to suc-≈ x              ≡⟨ refl (suc x) ⟩∎
    suc x                       ∎
    where
      open _≈_ (≡≈≈ ℤ ℤ)

  subst-C-sym-loop : ∀ x → subst C (sym loop) x ≡ pred x
  subst-C-sym-loop x = subst-sym C loop x (pred x) $
    subst C loop (pred x)            ≡⟨ subst-C-loop (pred x) ⟩
    suc (pred x)                     ≡⟨ suc-pred x ⟩∎
    x                                ∎

  -- The counting function
  S¹≡→ℤ : base ≡ base → ℤ
  S¹≡→ℤ p = subst C p zero

  right-inverse-of-pos : ∀ n → S¹≡→ℤ (ℤ→S¹≡ (pos n)) ≡ pos n
  right-inverse-of-pos ℕzero = 
      subst C (trans (refl base) loop) zero     ≡⟨ refl _ ⟩
      subst C loop zero                         ≡⟨ subst-C-loop zero ⟩∎
      pos ℕzero                                 ∎
  right-inverse-of-pos (ℕsuc n) = 
      subst C (trans (looping (ℕsuc n) loop) loop) zero   ≡⟨ subst-trans C (looping (ℕsuc n) loop) loop zero ⟩
      subst C loop (subst C (looping (ℕsuc n) loop) zero) ≡⟨ cong (subst C loop) $ right-inverse-of-pos n ⟩
      subst C loop (pos n)                                ≡⟨ subst-C-loop (pos n) ⟩∎
      pos (ℕsuc n)                                        ∎

  right-inverse-of-neg : ∀ n → S¹≡→ℤ (ℤ→S¹≡ (neg n)) ≡ neg n
  right-inverse-of-neg ℕzero = 
      subst C (trans (refl base) (sym loop)) zero     ≡⟨ refl _ ⟩
      subst C (sym loop) zero                         ≡⟨ subst-C-sym-loop zero ⟩∎
      neg ℕzero                                       ∎
  right-inverse-of-neg (ℕsuc n) = 
      subst C (trans (looping (ℕsuc n) (sym loop)) (sym loop)) zero   ≡⟨ subst-trans C (looping (ℕsuc n) (sym loop)) (sym loop) zero ⟩
      subst C (sym loop) (subst C (looping (ℕsuc n) (sym loop)) zero) ≡⟨ cong (subst C (sym loop)) $ right-inverse-of-neg n ⟩
      subst C (sym loop) (neg n)                                      ≡⟨ subst-C-sym-loop (neg n) ⟩∎
      neg (ℕsuc n)                                                    ∎

  right-inverse-of : ∀ z → S¹≡→ℤ (ℤ→S¹≡ z) ≡ z
  right-inverse-of zero = refl _
  right-inverse-of (pos n) = right-inverse-of-pos n
  right-inverse-of (neg n) = right-inverse-of-neg n

