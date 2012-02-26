------------------------------------------------------------------------
-- Paths in circles
------------------------------------------------------------------------

open import Prelude renaming (zero to ℕzero; suc to ℕsuc )
open import Equality
import Univalence-axiom

module Equality.Circle
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive)
  (univ : ∀ {ℓ} (A : Set ℓ) (B : Set ℓ) → Univalence-axiom.Univalence-axiom′ eq A B) where

open Derived-definitions-and-properties eq
import Equality.Tactic; open Equality.Tactic eq
import Equality.Misc; open Equality.Misc eq

private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection hiding (_∘_; id)

private
  module Weak where
    import Weak-equivalence; open Weak-equivalence eq public
open Weak hiding (_∘_; id)

open Univalence-axiom eq
import Univalence.Misc; open Univalence.Misc eq univ

import HigherInductive.Sphere; open HigherInductive.Sphere eq

------------------------------------------------------------------------
-- Simple ℤ implementation

-- Note that ⟦ pos n ⟧ = n + 1 and ⟦ neg n ⟧ = - (n + 1)

data ℤ : Set where
  pos : ℕ → ℤ
  neg : ℕ → ℤ
  zero : ℤ

------------------------------------------------------------------------
-- From ℤ to paths

private
  ℕ→S¹≡ : ℕ → base ≡ base
  ℕ→S¹≡ ℕzero = refl base
  ℕ→S¹≡ (ℕsuc n) = trans loop (ℕ→S¹≡ n)

ℤ→S¹≡ : ℤ → base ≡ base
ℤ→S¹≡ zero = refl base
ℤ→S¹≡ (pos n) = trans loop (ℕ→S¹≡ n)
ℤ→S¹≡ (neg n) = sym $ trans loop (ℕ→S¹≡ n)

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
    subst id suc-≡ x            ≡⟨ subst-id-≡ suc-≡ x ⟩
    _≈_.to (≡⇒≈ suc-≡) x        ≡⟨ cong (λ weq → _≈_.to weq x) $ univ-right-inverse-of suc-≈ ⟩
    _≈_.to suc-≈ x              ≡⟨ refl (suc x) ⟩∎
    suc x                       ∎

  -- The counting function
  S¹≡→ℤ : base ≡ base → ℤ
  S¹≡→ℤ p = subst C p zero

  -- For some reason Agda 2.3.0 crashed and printed:
  --
  --    An internal error has occurred. Please report this as a bug.
  --    Location of the error: src/full/Agda/TypeChecking/Conversion.hs:374
  --
  right-inverse-of-pos : ∀ n → S¹≡→ℤ (ℤ→S¹≡ (pos n)) ≡ pos n
  right-inverse-of-pos ℕzero = 
      subst C (trans loop (refl base)) zero     ≡⟨ cong (λ p → subst C p zero) $ trans-reflʳ _ ⟩
      subst C loop zero                         ≡⟨ subst-C-loop zero ⟩∎
      pos ℕzero                                 ∎
  right-inverse-of-pos (ℕsuc n) = 
      subst C (trans loop (trans loop (ℕ→S¹≡ n))) zero    ≡⟨ cong (λ p → subst C p zero) $ subst-trans C loop _ zero ⟩
      subst C loop (subst C (trans loop (ℕ→S¹≡ n)) zero)  ≡⟨ subst-C-loop _ ⟩
      suc (subst C (trans loop (ℕ→S¹≡ n)) zero)           ≡⟨ right-inverse-of-pos n ⟩∎
      pos (ℕsuc n)                                        ∎
