------------------------------------------------------------------------
-- Construction of Hopf junior
------------------------------------------------------------------------

-- A warmup for the Hopf fibration (the Hopf junior fibration)
-- which is a fibration for S⁰ → S¹ → S¹. The goal of this file
-- is to give the construction and show that the total space is
-- really S¹.

-- {-# OPTIONS --without-K #-}

-- Credits:
--  * Chris Kapulkin gave the construction of the Hopf (junior)
--  * Danial Licata gave the outline of almost all interesting parts

open import Prelude
open import Equality
import Univalence-axiom

module HigherInductive.Hopf-junior
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive)
  (univ : ∀ {ℓ} (A : Set ℓ) (B : Set ℓ) → Univalence-axiom.Univalence-axiom′ eq A B) where

open Derived-definitions-and-properties eq
import Equality.Tactic; open Equality.Tactic eq
import Equality.Misc; open Equality.Misc eq
import Equality.Sum; open Equality.Sum eq

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
-- Construction: apply S¹-rec to a non-trivial bijection in S⁰

private
  not-↔ : Bool ↔ Bool
  not-↔ = record
    { surjection = record
      { equivalence = record
        { to = not
        ; from = not
        }
      ; right-inverse-of = not-not
      }
    ; left-inverse-of = not-not
    }
    where
      not-not : ∀ x → not (not x) ≡ x
      not-not true = refl true
      not-not false = refl false

  not-≈ : Bool ≈ Bool
  not-≈ = ↔⇒≈ not-↔

  not-≡ : Bool ≡ Bool
  not-≡ = ≈⇒≡ not-≈

-- Here's the Hopf junior
Hj : S¹ → Set
Hj = S¹-rec[simp] Bool not-≡

------------------------------------------------------------------------
-- A map from S¹ to the total space of Hopf junior fibration

private
  -- "subst Hj loop" is "not"
  subst-Hj-loop : ∀ (x : Bool) → subst Hj loop x ≡ not x
  subst-Hj-loop x =
    subst Hj loop x             ≡⟨ sym $ subst-id-cong Hj loop x ⟩
    subst id (cong Hj loop) x   ≡⟨ cong (λ p → subst id p x) $ cong-S¹-rec[simp]-loop Bool not-≡ ⟩
    subst id not-≡ x            ≡⟨ subst-id-≡ not-≡ x ⟩
    _≈_.to (≡⇒≈ not-≡) x        ≡⟨ cong (λ weq → _≈_.to weq x) $ univ-right-inverse-of not-≈ ⟩
    _≈_.to not-≈ x              ≡⟨ refl (not x) ⟩∎
    not x                       ∎

  double-base-true : Σ S¹ Hj
  double-base-true = (base , true)

  double-base-false : Σ S¹ Hj
  double-base-false = (base , false)

  double-path-true-false : double-base-true ≡ double-base-false
  double-path-true-false = Σ≡→≡Σ Hj (loop , subst-Hj-loop true )

  double-path-false-true : double-base-false ≡ double-base-true
  double-path-false-true = Σ≡→≡Σ Hj (loop , subst-Hj-loop false )

  -- the map
  double : S¹ → Σ S¹ Hj
  double = S¹-rec[simp] double-base double-loop
    where
      -- new base
      double-base : Σ S¹ Hj
      double-base = double-base-true

      -- new loop
      double-loop : double-base ≡ double-base
      double-loop = trans double-path-true-false double-path-false-true

------------------------------------------------------------------------
-- A map from the total space to S¹

private
  halve′-base : Bool → S¹
  halve′-base _ = base

  -- the interesting loop
  halve′-loop : halve′-base ≡ halve′-base
  halve′-loop = extensionality′ (λ b → if b then loop else (refl _))

  -- the boring loop
  halve′-boring-loop′ : ∀ x → subst (λ (x : S¹) → Hj x → S¹) loop halve′-base x ≡ halve′-base x
  halve′-boring-loop′ x =
      subst (λ (x : S¹) → Hj x → S¹) loop halve′-base x             ≡⟨ subst-func Hj (const S¹) loop halve′-base x ⟩
      subst (const S¹) loop (halve′-base (subst Hj (sym loop) x))   ≡⟨ refl _ ⟩
      subst (const S¹) loop base                                    ≡⟨ subst-const loop base ⟩∎
      base                                                          ∎
  halve′-boring-loop : subst (λ (x : S¹) → Hj x → S¹) loop halve′-base ≡ halve′-base
  halve′-boring-loop = extensionality′ halve′-boring-loop′

  halve′ : (x : S¹) → Hj x → S¹
  halve′ = S¹-rec (λ x → Hj x → S¹) halve′-base (trans halve′-boring-loop halve′-loop)

  -- the map
  halve : Σ S¹ Hj → S¹
  halve (x , y) = halve′ x y

------------------------------------------------------------------------
-- Bijection

