------------------------------------------------------------------------
-- Construction of Hopf junior
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- {-# OPTIONS --without-K #-}

-- A warmup for the Hopf fibration (the Hopf junior fibration)
-- which is a fibration for S⁰ → S¹ → S¹. The goal of this file
-- is to give the construction and show that the total space is
-- really S¹.

-- Credits:
--  * Peter Lumsdaine gave the construction of the Hopf (junior)
--  * Danial Licata gave the outline of almost all interesting parts

open import Univalence

module HigherInductive.Hopf-junior
  (univ : ∀ {ℓ} (A B : Set ℓ) → Univalence-axiom A B) where

open import Prelude
open import Path
open import Path.Lemmas
open import Path.Sum
open import Bijection hiding (_∘_; id)
open import Weak-equivalence as Weak hiding (_∘_; id)

import Univalence.Lemmas; open Univalence.Lemmas univ
import Univalence.Extensionality; open Univalence.Extensionality univ

open import HigherInductive.Sphere

------------------------------------------------------------------------
-- Construction: apply S¹-rec to a non-trivial bijection in S⁰

private
  not-not : ∀ x → not (not x) ≡ x
  not-not true = refl true
  not-not false = refl false

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
  abstract
    -- "subst Hj loop" is "not"
    subst-Hj-loop : ∀ (x : Bool) → subst Hj loop x ≡ not x
    subst-Hj-loop x =
      subst Hj loop x             ≡⟨ sym $ subst-id-cong Hj loop x ⟩
      subst id (cong Hj loop) x   ≡⟨ cong (λ p → subst id p x) $ cong-S¹-rec[simp]-loop Bool not-≡ ⟩
      subst id not-≡ x            ≡⟨ subst-id-univ not-≡ x ⟩
      _≈_.to (≡⇒≈ not-≡) x        ≡⟨ cong (λ weq → _≈_.to weq x) $ right-inverse-of not-≈ ⟩∎
--    to not-≈ x                  ≡⟨ refl (not x) ⟩∎
      not x                       ∎
      where
        open _≈_ (≡≈≈ Bool Bool)

  double-base-true : Σ S¹ Hj
  double-base-true = (base , true)

  double-base-false : Σ S¹ Hj
  double-base-false = (base , false)

  double-path-true→false : double-base-true ≡ double-base-false
  double-path-true→false = Σ≡⇒≡Σ Hj (loop , subst-Hj-loop true )

  double-path-false→true : double-base-false ≡ double-base-true
  double-path-false→true = Σ≡⇒≡Σ Hj (loop , subst-Hj-loop false )
  
  double-base : Σ S¹ Hj
  double-base = double-base-true

  double-loop : double-base ≡ double-base
  double-loop = trans double-path-true→false double-path-false→true

  -- the map
  double : S¹ → Σ S¹ Hj
  double = S¹-rec[simp] double-base double-loop

------------------------------------------------------------------------
-- A map from the total space to S¹

private
  halve′-base : Bool → S¹
  halve′-base _ = base

  -- the interesting loop
  halve′-loop′ : ∀ x → halve′-base x ≡ halve′-base x
  halve′-loop′ true = loop
  halve′-loop′ false = refl base

  halve′-loop : halve′-base ≡ halve′-base
  halve′-loop = ext halve′-loop′

  -- the boring loop
  halve′-boring-loop′ : ∀ x → subst (λ (x : S¹) → Hj x → S¹) loop halve′-base x ≡ halve′-base x
  halve′-boring-loop′ true =
      subst (λ (x : S¹) → Hj x → S¹) loop halve′-base true          ≡⟨ sym $ subst-app Hj (const S¹) loop halve′-base (subst-Hj-loop false) ⟩
      subst (const S¹) loop (halve′-base (subst Hj loop false))     ≡⟨ refl _ ⟩
      subst (const S¹) loop base                                    ≡⟨ subst-const loop base ⟩∎
      base                                                          ∎
  halve′-boring-loop′ false =
      subst (λ (x : S¹) → Hj x → S¹) loop halve′-base false         ≡⟨ sym $ subst-app Hj (const S¹) loop halve′-base (subst-Hj-loop true) ⟩
      subst (const S¹) loop (halve′-base (subst Hj loop true))      ≡⟨ refl _ ⟩
      subst (const S¹) loop base                                    ≡⟨ subst-const loop base ⟩∎
      base                                                          ∎

  halve′-boring-loop : subst (λ (x : S¹) → Hj x → S¹) loop halve′-base ≡ halve′-base
  halve′-boring-loop = ext halve′-boring-loop′

  halve′ : (x : S¹) → Hj x → S¹
  halve′ = S¹-rec (λ x → Hj x → S¹) halve′-base (trans halve′-boring-loop halve′-loop)

  -- the map
  halve : Σ S¹ Hj → S¹
  halve = uncurry halve′

------------------------------------------------------------------------
-- Bijection

-- Sorry for the ugly proof.

private
  abstract
    -- This lemma is the most interesting (difficult) one!
    cong-halve-double-path : ∀ b → cong halve (Σ≡⇒≡Σ Hj (loop , subst-Hj-loop b)) ≡ halve′-loop′ (not b)
    cong-halve-double-path true =
      cong halve (Σ≡⇒≡Σ Hj (loop , subst-Hj-loop true))
        ≡⟨ cong-Σ≡⇒≡Σ Hj S¹ halve′ loop (subst-Hj-loop true) ⟩
              (base                                                     ≡⟨ line₁ ⟩
               subst (const S¹) loop base                               ≡⟨ line₂ ⟩
               subst (λ x → Hj x → S¹) loop halve′-base false           ≡⟨ line₃ ⟩∎
               base                                                     ∎)
        ≡⟨ refl _ ⟩
            trans line₁ (trans line₂ line₃)
        ≡⟨ cong (trans line₁ ∘ trans line₂) $ lemma₃ ⟩
            trans line₁ (trans line₂ (trans line₃′|₁ line₃′|₂))
        ≡⟨ cong (trans line₁) $ trans-transʳ-sym line₂ line₃′|₂ ⟩
            trans line₁ line₃′|₂
        ≡⟨ trans-symˡ line₃′|₂ ⟩∎
            refl _
        ∎
      where
        line₁ : base ≡ subst (const S¹) loop base 
        line₁ = sym $ subst-const loop base 
        line₂ : subst (const S¹) loop base ≡ subst (λ x → Hj x → S¹) loop halve′-base false
        line₂ = subst-app Hj (const S¹) loop halve′-base (subst-Hj-loop true)
        line₃ : subst (λ x → Hj x → S¹) loop halve′-base false ≡ base
        line₃ = cong (λ f′ → f′ false) $ cong[dep] (λ x → Hj x → S¹) halve′ loop
  
        line₃′|₁ : subst (λ (x : S¹) → Hj x → S¹) loop halve′-base false ≡ subst (const S¹) loop base
        line₃′|₁ = sym $ subst-app Hj (const S¹) loop halve′-base (subst-Hj-loop true) 
        line₃′|₂ : subst (const S¹) loop base ≡ base
        line₃′|₂ = subst-const loop base

        abstract
          lemma₃ : line₃ ≡ trans line₃′|₁ line₃′|₂
          lemma₃ =
            line₃
                ≡⟨ cong (cong (λ f → f false)) $ cong[dep]-S¹-rec-loop (λ x → Hj x → S¹) halve′-base _ ⟩
            cong (λ f → f false) (trans halve′-boring-loop halve′-loop)
                ≡⟨ cong-trans (λ f → f false) halve′-boring-loop halve′-loop ⟩
            trans (cong (λ f → f false) halve′-boring-loop) (cong (λ f → f false) halve′-loop)
                ≡⟨ cong (trans $ cong (λ f → f false) halve′-boring-loop) $ ext-elim halve′-loop′ false ⟩
            trans (cong (λ f → f false) halve′-boring-loop) (halve′-loop′ false)
                ≡⟨ trans-reflʳ $ cong (λ f → f false) halve′-boring-loop ⟩
            cong (λ f → f false) halve′-boring-loop
                ≡⟨ ext-elim halve′-boring-loop′ false ⟩
            halve′-boring-loop′ false
                ≡⟨ refl _ ⟩∎
            trans line₃′|₁ line₃′|₂
                ∎
 
    cong-halve-double-path false =
      cong halve (Σ≡⇒≡Σ Hj (loop , subst-Hj-loop false))
        ≡⟨ cong-Σ≡⇒≡Σ Hj S¹ halve′ loop (subst-Hj-loop false) ⟩
              (base                                                     ≡⟨ line₁ ⟩
               subst (const S¹) loop base                               ≡⟨ line₂ ⟩
               subst (λ x → Hj x → S¹) loop halve′-base true            ≡⟨ line₃ ⟩∎
               base                                                     ∎)
        ≡⟨ refl _ ⟩
            trans line₁ (trans line₂ line₃)
        ≡⟨ cong (trans line₁ ∘ trans line₂) $ lemma₃ ⟩
            trans line₁ (trans line₂ (trans line₃′|₁ (trans line₃′|₂ loop)))
        ≡⟨ cong (trans line₁) $ trans-transʳ-sym line₂ (trans line₃′|₂ loop) ⟩
            trans line₁ (trans line₃′|₂ loop)
        ≡⟨ trans-sym-trans line₃′|₂ loop ⟩∎
            loop
        ∎
      where
        line₁ : base ≡ subst (const S¹) loop base 
        line₁ = sym $ subst-const loop base 
        line₂ : subst (const S¹) loop base ≡ subst (λ x → Hj x → S¹) loop halve′-base true
        line₂ = subst-app Hj (const S¹) loop halve′-base (subst-Hj-loop false)
        line₃ : subst (λ x → Hj x → S¹) loop halve′-base true ≡ base
        line₃ = cong (λ f′ → f′ true) $ cong[dep] (λ x → Hj x → S¹) halve′ loop
  
        line₃′|₁ : subst (λ (x : S¹) → Hj x → S¹) loop halve′-base true ≡ subst (const S¹) loop base
        line₃′|₁ = sym $ subst-app Hj (const S¹) loop halve′-base (subst-Hj-loop false)
        line₃′|₂ : subst (const S¹) loop base ≡ base
        line₃′|₂ = subst-const loop base
  
        abstract
          lemma₃ : line₃ ≡ trans line₃′|₁ (trans line₃′|₂ loop)
          lemma₃ =
            line₃
                ≡⟨ cong (cong (λ f → f true)) $ cong[dep]-S¹-rec-loop (λ x → Hj x → S¹) halve′-base _ ⟩
            cong (λ f → f true) (trans halve′-boring-loop halve′-loop)
                ≡⟨ cong-trans (λ f → f true) halve′-boring-loop halve′-loop ⟩
            trans (cong (λ f → f true) halve′-boring-loop) (cong (λ f → f true) halve′-loop)
                ≡⟨ cong (trans $ cong (λ f → f true) halve′-boring-loop) $ ext-elim halve′-loop′ true ⟩
            trans (cong (λ f → f true) halve′-boring-loop) (halve′-loop′ true)
                ≡⟨ refl _ ⟩
            trans (cong (λ f → f true) halve′-boring-loop) loop
                ≡⟨ cong (λ p → trans p loop) $ ext-elim halve′-boring-loop′ true ⟩
            trans (halve′-boring-loop′ true) loop
                ≡⟨ trans-assoc line₃′|₁ line₃′|₂ loop ⟩∎
            trans line₃′|₁ (trans line₃′|₂ loop)
                ∎

private
  cong-halve-double-loop : cong halve double-loop ≡ loop
  cong-halve-double-loop =
      cong halve double-loop
          ≡⟨ cong-trans halve double-path-true→false double-path-false→true ⟩
      trans (cong halve double-path-true→false) (cong halve double-path-false→true)
          ≡⟨ cong (trans (cong halve double-path-true→false)) $ cong-halve-double-path false ⟩
      trans (cong halve double-path-true→false) loop
          ≡⟨ cong (λ p → trans p loop) $ cong-halve-double-path true ⟩∎
      loop
          ∎
  
  cong-double-loop : cong double loop ≡ double-loop
  cong-double-loop = cong-S¹-rec[simp]-loop double-base double-loop

S¹↔ΣS¹Hj : S¹ ↔ Σ S¹ Hj
S¹↔ΣS¹Hj =
  record
  { surjection = record
    { equivalence = record
      { to = double
      ; from = halve
      }
    ; right-inverse-of = right-inverse-of
    }
  ; left-inverse-of = left-inverse-of
  }
  where
    left-inverse-of : ∀ x → halve (double x) ≡ x
    left-inverse-of = S¹-rec (λ x → halve (double x) ≡ x) (refl base) ≡-loop
      where
        ≡-loop : subst (λ x → halve (double x) ≡ x) loop (refl base) ≡ refl base
        ≡-loop =
          subst (λ x → halve (double x) ≡ x) loop (refl base)       ≡⟨ subst-path[id] (halve ∘ double) loop (refl base) ⟩
          trans (sym (cong (halve ∘ double) loop)) loop             ≡⟨ cong (λ p → trans (sym p) loop) $ sym $ cong-cong halve double loop ⟩
          trans (sym (cong halve $ cong double loop)) loop          ≡⟨ cong (λ p → trans (sym (cong halve p)) loop) $ cong-double-loop ⟩
          trans (sym (cong halve double-loop)) loop                 ≡⟨ cong (λ p → trans (sym p) loop) $ cong-halve-double-loop ⟩
          trans (sym loop) loop                                     ≡⟨ trans-symˡ loop ⟩∎
          refl base                                                 ∎

    right-inverse-of : ∀ s → double (halve s) ≡ s
    right-inverse-of = uncurry left-inverse-of′
      where
        ≡-base : ∀ b → double (halve (base , b)) ≡ (base , b)
        ≡-base true = refl _
        ≡-base false = double-path-true→false

        ≡-loop′ : ∀ b → subst (λ x → (y : Hj x) → double (halve (x , y)) ≡ (x , y)) loop ≡-base b ≡ ≡-base b

        -- false → true
        ≡-loop′ true =
          subst (λ x → (y : Hj x) → double (halve (x , y)) ≡ (x , y)) loop ≡-base true
              ≡⟨ subst-Σfunc Hj (λ s → double (halve s) ≡ s) loop ≡-base (subst-Hj-loop false) ⟩
          subst (λ s → double (halve s) ≡ s) double-path-false→true double-path-true→false
              ≡⟨ subst-path[id] (double ∘ halve) double-path-false→true double-path-true→false ⟩
          trans (sym (cong (double ∘ halve) double-path-false→true)) double-loop
              ≡⟨ cong (λ p → trans (sym p) double-loop) $ sym $ cong-cong double halve double-path-false→true ⟩
          trans (sym (cong double $ cong halve double-path-false→true)) double-loop
              ≡⟨ cong (λ p → trans (sym (cong double $ p)) double-loop) $ cong-halve-double-path false ⟩
          trans (sym (cong double loop)) double-loop
              ≡⟨ cong (λ p → trans (sym p) double-loop) cong-double-loop ⟩
          trans (sym double-loop) double-loop
              ≡⟨ trans-symˡ double-loop ⟩∎
          refl _
              ∎

        -- true → false
        ≡-loop′ false =
          subst (λ x → (y : Hj x) → double (halve (x , y)) ≡ (x , y)) loop ≡-base false
              ≡⟨ subst-Σfunc Hj (λ s → double (halve s) ≡ s) loop ≡-base (subst-Hj-loop true) ⟩
          subst (λ s → double (halve s) ≡ s) double-path-true→false (refl _)
              ≡⟨ subst-path[id] (double ∘ halve) double-path-true→false (refl _) ⟩
          trans (sym (cong (double ∘ halve) double-path-true→false)) double-path-true→false
              ≡⟨ cong (λ p → trans (sym p) double-path-true→false) $ sym $ cong-cong double halve double-path-true→false ⟩
          trans (sym (cong double $ cong halve double-path-true→false)) double-path-true→false
              ≡⟨ cong (λ p → trans (sym (cong double $ p)) double-path-true→false) $ cong-halve-double-path true ⟩∎
          double-path-true→false
              ∎

        ≡-loop : subst (λ x → (y : Hj x) → double (halve (x , y)) ≡ (x , y)) loop ≡-base ≡ ≡-base
        ≡-loop = ext[dep] ≡-loop′

        left-inverse-of′ =
          S¹-rec (λ x → (y : Hj x) → double (halve (x , y)) ≡ (x , y)) ≡-base ≡-loop
