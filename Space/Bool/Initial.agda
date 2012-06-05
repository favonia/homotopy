------------------------------------------------------------------------
-- Alternative axioms for Boolean
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- Two equivalent ways to axiomatize Boolean
-- with extensionality for functions:
--  (1) non-dependent elim + being inital
--  (2) dependent elim

{-# OPTIONS --without-K #-}

-- Credits:
--  * Kristina Sojakova stated the theorem and gave a proof in 2011 Nov
--    but I was too inexperienced to understand it back then.
--  * The direction from "homotopy" to "dependent elim" is done by
--    myself (Favonia) as an Agda exercise. The other direction
--    should not be hard with extensionalty for functions...

module Space.Bool.Initial where

open import Prelude hiding (Bool; true; false; if_then_else_)
open import Path
open import Path.Lemmas
open import Path.Sum

private
  subst-× : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} (B : A → Set ℓ₂) (C : A → Set ℓ₃)
                  {x y : A} (p : x ≡ y) (bx : B x) (cx : C x) →
                  subst (λ x → (B x) × (C x)) p (bx , cx) ≡ (subst B p bx , subst C p cx)
  subst-× B C =
    elim
      (λ {x y} p → (bx : B x) (cx : C x) →
          subst (λ x → (B x) × (C x)) p (bx , cx) ≡ (subst B p bx , subst C p cx))
      (λ x bx cx → refl _)

record Bool-axiom {ℓ} : Set (lsuc ℓ) where
  field
    {- form -}
    Bool : Set ℓ
    {- intro -}
    true false : Bool
    {- elim -}
    if : ∀ (C : Bool → Set ℓ) (b : Bool) → C true → C false → C b
    {- conv -}
    if-true  : ∀ (C : Bool → Set ℓ) (et : C true) (ef : C false) → if C true  et ef ≡ et 
    if-false : ∀ (C : Bool → Set ℓ) (et : C true) (ef : C false) → if C false et ef ≡ ef

record Bool-axiom′ {ℓ} : Set (lsuc ℓ) where
  field
    {- form -}
    Bool : Set ℓ
    {- intro -}
    true false : Bool
    {- elim -}
    if : ∀ {C : Set ℓ} → Bool → C → C → C
    {- conv -}
    if-true  : ∀ {C : Set ℓ} (et ef : C) → if true  et ef ≡ et 
    if-false : ∀ {C : Set ℓ} (et ef : C) → if false et ef ≡ ef
    
    hom : ∀ {C : Set ℓ} {et ef : C} (h : Bool → C) →
          (vt : h true ≡ et) (vf : h false ≡ ef) →
          _≡_ {A = Σ (Bool → C) (λ h′ → (h′ true ≡ et) × (h′ false ≡ ef))}
          (h                  , (vt                    , vf            ))
          ((λ b → if b et ef) , (if-true et ef         , if-false et ef))

  private
    -- A module to extact information out of the hom axiom
    module HomModule {C : Set ℓ} {et ef : C} (h : Bool → C) (vt′ : h true ≡ et) (vf′ : h false ≡ ef) where
      vt = vt′
      vf = vf′

      private
        lemma-hom = ≡Σ⇒Σ≡ (λ h′ → (h′ true ≡ et) × (h′ false ≡ ef)) $ hom h vt vf

      path-h = proj₁ lemma-hom

      private
        lemma-true-false = ≡×⇒×≡ $
          (subst (λ h′ → (h′ true ≡ et)) path-h vt , subst (λ h′ → (h′ false ≡ ef)) path-h vf)
              ≡⟨ sym $ subst-× (λ h′ → (h′ true ≡ et)) (λ h′ → (h′ false ≡ ef)) path-h vt vf ⟩
          subst (λ h′ → (h′ true ≡ et) × (h′ false ≡ ef)) path-h (vt , vf)
              ≡⟨ proj₂ lemma-hom ⟩∎
          (if-true et ef , if-false et ef)
              ∎

      abstract
        path-true : subst (λ h → (h true ≡ et)) path-h vt ≡ if-true et ef
        path-true = proj₁ lemma-true-false
        path-false : subst (λ h → (h false ≡ ef)) path-h vf ≡ if-false et ef
        path-false = proj₂ lemma-true-false

        sym-cong-true-h : trans (sym (cong (λ f → f true) path-h)) vt ≡ if-true et ef
        sym-cong-true-h =
          trans (sym (cong (λ f → f true) path-h)) vt
              ≡⟨ sym $ subst-path[constʳ] (λ f → f true) et path-h vt ⟩
          subst (λ h → (h true ≡ et)) path-h vt
              ≡⟨ path-true ⟩∎
          if-true et ef
              ∎
  
        sym-cong-false-h : trans (sym (cong (λ f → f false) path-h)) vf ≡ if-false et ef
        sym-cong-false-h =
          trans (sym (cong (λ f → f false) path-h)) vf
              ≡⟨ sym $ subst-path[constʳ] (λ f → f false) ef path-h vf ⟩
          subst (λ h → (h false ≡ ef)) path-h vf
              ≡⟨ path-false ⟩∎
          if-false et ef
              ∎

    -- A module to provide a nice dependent "if" interface
    module IfModule (C : Bool → Set ℓ) (et : C true) (ef : C false) where
      private
        et′ : Σ Bool C
        et′ = (true , et)
        ef′ : Σ Bool C
        ef′ = (false , ef)

        module ID = HomModule id (refl true) (refl false)

        module Proj₁ = HomModule
          (λ b → proj₁ (if b et′ ef′))
          (cong proj₁ (if-true et′ ef′))
          (cong proj₁ (if-false et′ ef′))

      if′ : ∀ (b : Bool) → C b
      if′ b = subst (λ f → C (f b)) (trans Proj₁.path-h (sym ID.path-h)) $ proj₂ (if b et′ ef′)

      abstract
        if′-true : if′ true ≡ et
        if′-true = 
          subst (λ f → C (f true)) (trans Proj₁.path-h (sym ID.path-h)) (proj₂ (if true et′ ef′))
              ≡⟨ sym $ subst-cong C (λ f → f true) (trans Proj₁.path-h (sym ID.path-h)) _ ⟩
          subst C (cong (λ f → f true) (trans Proj₁.path-h (sym ID.path-h))) (proj₂ (if true et′ ef′))
              ≡⟨ cong (λ p → subst C p $ proj₂ (if true et′ ef′)) $ cong-trans (λ f → f true) Proj₁.path-h (sym ID.path-h) ⟩
          subst C (trans (cong (λ f → f true) Proj₁.path-h) (cong (λ f → f true) (sym ID.path-h))) (proj₂ (if true et′ ef′))
              ≡⟨ cong (λ p → subst C (trans (cong (λ f → f true) Proj₁.path-h) p) $ proj₂ (if true et′ ef′)) $ cong-sym (λ f → f true) ID.path-h ⟩
          subst C (trans (cong (λ f → f true) Proj₁.path-h) (sym $ cong (λ f → f true) ID.path-h)) (proj₂ (if true et′ ef′))
              ≡⟨ cong (λ p → subst C (trans (cong (λ f → f true) Proj₁.path-h) p) $ proj₂ (if true et′ ef′)) $
                  sym $ trans-reflʳ (sym $ cong (λ f → f true) ID.path-h) ⟩
          subst C (trans (cong (λ f → f true) Proj₁.path-h) (trans (sym $ cong (λ f → f true) ID.path-h) (refl true))) (proj₂ (if true et′ ef′))
              ≡⟨ cong (λ p → subst C (trans (cong (λ f → f true) Proj₁.path-h) p) $ proj₂ (if true et′ ef′)) $ ID.sym-cong-true-h ⟩
          subst C (trans (cong (λ f → f true) Proj₁.path-h) (if-true true false)) (proj₂ (if true et′ ef′))
              ≡⟨ cong (λ p → subst C (trans (cong (λ f → f true) Proj₁.path-h) p) $ proj₂ (if true et′ ef′)) $ sym $ Proj₁.sym-cong-true-h ⟩
          subst C (trans (cong (λ f → f true) Proj₁.path-h) (trans (sym (cong (λ f → f true) Proj₁.path-h)) Proj₁.vt)) (proj₂ (if true et′ ef′))
              ≡⟨ cong (λ p → subst C p $ proj₂ (if true et′ ef′)) $ trans-transʳ-sym (cong (λ f → f true) Proj₁.path-h) _ ⟩
          subst C Proj₁.vt (proj₂ (if true et′ ef′))
              ≡⟨ subst-cong C proj₁ (if-true et′ ef′) $ proj₂ (if true et′ ef′) ⟩
          subst (C ∘ proj₁) (if-true et′ ef′) (proj₂ (if true et′ ef′))
              ≡⟨ cong[dep]  (λ s → C (proj₁ s)) proj₂ (if-true et′ ef′) ⟩∎
          proj₂ et′
              ∎

        if′-false : if′ false ≡ ef
        if′-false = 
          subst (λ f → C (f false)) (trans Proj₁.path-h (sym ID.path-h)) (proj₂ (if false et′ ef′))
              ≡⟨ sym $ subst-cong C (λ f → f false) (trans Proj₁.path-h (sym ID.path-h)) _ ⟩
          subst C (cong (λ f → f false) (trans Proj₁.path-h (sym ID.path-h))) (proj₂ (if false et′ ef′))
              ≡⟨ cong (λ p → subst C p $ proj₂ (if false et′ ef′)) $ cong-trans (λ f → f false) Proj₁.path-h (sym ID.path-h) ⟩
          subst C (trans (cong (λ f → f false) Proj₁.path-h) (cong (λ f → f false) (sym ID.path-h))) (proj₂ (if false et′ ef′))
              ≡⟨ cong (λ p → subst C (trans (cong (λ f → f false) Proj₁.path-h) p) $ proj₂ (if false et′ ef′)) $ cong-sym (λ f → f false) ID.path-h ⟩
          subst C (trans (cong (λ f → f false) Proj₁.path-h) (sym $ cong (λ f → f false) ID.path-h)) (proj₂ (if false et′ ef′))
              ≡⟨ cong (λ p → subst C (trans (cong (λ f → f false) Proj₁.path-h) p) $ proj₂ (if false et′ ef′)) $
                  sym $ trans-reflʳ (sym $ cong (λ f → f false) ID.path-h) ⟩
          subst C (trans (cong (λ f → f false) Proj₁.path-h) (trans (sym $ cong (λ f → f false) ID.path-h) (refl false))) (proj₂ (if false et′ ef′))
              ≡⟨ cong (λ p → subst C (trans (cong (λ f → f false) Proj₁.path-h) p) $ proj₂ (if false et′ ef′)) $ ID.sym-cong-false-h ⟩
          subst C (trans (cong (λ f → f false) Proj₁.path-h) (if-false true false)) (proj₂ (if false et′ ef′))
              ≡⟨ cong (λ p → subst C (trans (cong (λ f → f false) Proj₁.path-h) p) $ proj₂ (if false et′ ef′)) $ sym $ Proj₁.sym-cong-false-h ⟩
          subst C (trans (cong (λ f → f false) Proj₁.path-h) (trans (sym (cong (λ f → f false) Proj₁.path-h)) Proj₁.vf)) (proj₂ (if false et′ ef′))
              ≡⟨ cong (λ p → subst C p $ proj₂ (if false et′ ef′)) $ trans-transʳ-sym (cong (λ f → f false) Proj₁.path-h) _ ⟩
          subst C Proj₁.vf (proj₂ (if false et′ ef′))
              ≡⟨ subst-cong C proj₁ (if-false et′ ef′) $ proj₂ (if false et′ ef′) ⟩
          subst (C ∘ proj₁) (if-false et′ ef′) (proj₂ (if false et′ ef′))
              ≡⟨ cong[dep]  (λ s → C (proj₁ s)) proj₂ (if-false et′ ef′) ⟩∎
          proj₂ ef′
              ∎

  if′ : ∀ (C : Bool → Set ℓ) (b : Bool) → C true → C false → C b
  if′ C b et ef = IfModule.if′ C et ef b

  if′-true : ∀ (C : Bool → Set ℓ) (et : C true) (ef : C false) → if′ C true et ef ≡ et
  if′-true C et ef = IfModule.if′-true C et ef

  if′-false : ∀ (C : Bool → Set ℓ) (et : C true) (ef : C false) → if′ C false et ef ≡ ef
  if′-false C et ef = IfModule.if′-false C et ef

