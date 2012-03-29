------------------------------------------------------------------------
-- Spheres (base + loop)
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

-- Currently we have S¹ and an experimental S²

{-# OPTIONS --without-K #-}

module Space.Sphere where

open import Prelude
open import Path
open import Path.Lemmas
open import Path.Sum
open import Path.Higher-order

------------------------------------------------------------------------
-- Safe area: S¹ only
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Formation rules and introduction rules

private
  data S¹′ : Set where
    base¹′ : S¹′

S¹ : Set
S¹ = S¹′

base¹ : S¹
base¹ = base¹′

base : S¹
base = base¹

-- Agda seems to think loop and refl are NOT definitionally equal
-- outside of this abstract block
abstract
  loop¹ : base¹ ≡ base¹
  loop¹ = refl base¹

loop : base ≡ base
loop = loop¹

------------------------------------------------------------------------
-- Elimination rules and computation rules

-- Dependent version

S¹-elim : ∀ {ℓ} (P : S¹ → Set ℓ) (pbase : P base) → subst P loop¹ pbase ≡ pbase → (x : S¹) → P x
S¹-elim _ pbase _ base¹′ = pbase

-- This is actually definitionally equality...
postulate
  S¹-elim-loop : ∀ {ℓ} (P : S¹ → Set ℓ) (pbase : P base) (ploop : subst P loop¹ pbase ≡ pbase)
                 → cong[dep] P (S¹-elim P pbase ploop) loop¹ ≡ ploop

-- Non-dependent version

S¹-elim[simp] : ∀ {ℓ} {P : Set ℓ} (pbase : P) → pbase ≡ pbase → S¹ → P
S¹-elim[simp] {P = P} pbase ploop = S¹-elim (const P) pbase (trans boring-loop ploop)
  where
    boring-loop = subst-const loop pbase

-- This propositional equality is derivable from the dependent version.
S¹-elim[simp]-loop : ∀ {ℓ} {P : Set ℓ} (pbase : P) (ploop : pbase ≡ pbase)
                         → cong (S¹-elim[simp] pbase ploop) loop¹ ≡ ploop
S¹-elim[simp]-loop {P = P} pbase ploop =
  cong dcircle loop¹                                                  ≡⟨ sym $ trans-sym-trans boring-loop _ ⟩
  trans (sym $ boring-loop) (trans boring-loop $ cong dcircle loop¹)  ≡⟨ cong (trans $ sym $ boring-loop) $ sym $ cong[dep]-const dcircle loop¹ ⟩
  trans (sym $ boring-loop) (cong[dep] (const P) dcircle loop¹)       ≡⟨ cong (trans $ sym $ boring-loop) $ S¹-elim-loop (const P) _ _ ⟩
  trans (sym $ boring-loop) (trans boring-loop ploop)                 ≡⟨ trans-sym-trans boring-loop _ ⟩∎
  ploop                                                               ∎
  where
    boring-loop = subst-const loop¹ pbase
    dcircle = S¹-elim[simp] pbase ploop

------------------------------------------------------------------------
-- Experimental area: S² and beyond!
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Formation rules and introduction rules

private
  data Sⁿ′ (n : ℕ) : Set where
    baseⁿ′ : Sⁿ′ n

Sⁿ : ℕ → Set
Sⁿ = Sⁿ′

baseⁿ : ∀ n → Sⁿ n
baseⁿ n = baseⁿ′

private
  S-endpoints⇑ : ∀ n {S : Set} → S → Endpoints⇑ n S
  S-loop⇑ : ∀ n {S : Set} (base : S) → Path⇑ n (S-endpoints⇑ n base)

  S-endpoints⇑ 0       base = lift tt
  S-endpoints⇑ (suc n) base = (S-endpoints⇑ n base , S-loop⇑ n base , S-loop⇑ n base)

  S-loop⇑ 0       base = base
  S-loop⇑ (suc n) base = refl (S-loop⇑ n base)

  Sⁿ-endpoints : ∀ n → Endpoints⇑ n (Sⁿ n)
  Sⁿ-endpoints n = S-endpoints⇑ n (baseⁿ n)

-- Agda seems to think these are NOT definitionally equal
abstract
  loopⁿ : ∀ n → Path⇑ n (Sⁿ-endpoints n)
  loopⁿ n = S-loop⇑ n (baseⁿ n)

private
  -- Some test cases for "Path⇑ n (Sⁿ-endpoints n)"
  -- Things need to be definitionally equal to what we expect in all finite cases.
  module Test₁ where
    test₀ : Path⇑ 0 (Sⁿ-endpoints 0) ≡ Sⁿ 0
    test₀ = refl _

    test₁ : Path⇑ 1 (Sⁿ-endpoints 1) ≡ (baseⁿ 1 ≡ baseⁿ 1)
    test₁ = refl _

    test₂ : Path⇑ 2 (Sⁿ-endpoints 2) ≡ (refl (baseⁿ 2) ≡ refl (baseⁿ 2))
    test₂ = refl _

private
  S-endpoints[dep]⇑ : ∀ {ℓ} n {S : Set} (P : S → Set ℓ) (base : S) (pbase : P base) →
                      Endpoints[dep]⇑ n P (S-endpoints⇑ n base)
  S-loop[dep]⇑ : ∀ {ℓ} n {S : Set} (P : S → Set ℓ) (base : S) (pbase : P base) →
                 Path[dep]⇑ n P (S-loop⇑ n base) (S-endpoints[dep]⇑ n P base pbase)

  S-endpoints[dep]⇑ 0       P base pbase = lift tt
  S-endpoints[dep]⇑ (suc n) P base pbase = (S-endpoints[dep]⇑ n P base pbase ,
                                            S-loop[dep]⇑ n P base pbase ,
                                            S-loop[dep]⇑ n P base pbase)

  S-loop[dep]⇑ 0       P base pbase = pbase
  S-loop[dep]⇑ (suc n) P base pbase = refl (S-loop[dep]⇑ n P base pbase)

  Sⁿ-endpoints[dep] : ∀ {ℓ} n (P : Sⁿ n → Set ℓ) → P (baseⁿ n) → Endpoints[dep]⇑ n P (Sⁿ-endpoints n)
  Sⁿ-endpoints[dep] n P pbase = S-endpoints[dep]⇑ n P (baseⁿ n) pbase

------------------------------------------------------------------------
-- Elimination rules and computation rules

-- Dependent version
Sⁿ-elim : ∀ {ℓ} n (P : Sⁿ n → Set ℓ) (pbase : P (baseⁿ n)) → Path[dep]⇑ n P (loopⁿ n) (Sⁿ-endpoints[dep] n P pbase) → ∀ x → P x
Sⁿ-elim n P pbase _ baseⁿ′ = pbase

private
  -- Some test cases for "Path[dep]⇑ n P (loopⁿ n) (Sⁿ-endpoints[dep] n P pbase)"
  module Test₂ where
    test₀ : ∀ {ℓ} (P : Sⁿ 0 → Set ℓ) (pbase : P (baseⁿ 0)) →
            Path[dep]⇑ 0 P (loopⁿ 0) (Sⁿ-endpoints[dep] 0 P pbase) ≡ P (loopⁿ 0)
    test₀ _ _ = refl _

    test₁ : ∀ {ℓ} (P : Sⁿ 1 → Set ℓ) (pbase : P (baseⁿ 1)) →
            Path[dep]⇑ 1 P (loopⁿ 1) (Sⁿ-endpoints[dep] 1 P pbase) ≡ (subst P (loopⁿ 1) pbase ≡ pbase)
    test₁ _ _ = refl _

    test₂ : ∀ {ℓ} (P : Sⁿ 2 → Set ℓ) (pbase : P (baseⁿ 2)) →
            Path[dep]⇑ 2 P (loopⁿ 2) (Sⁿ-endpoints[dep] 2 P pbase) ≡ (subst (λ p → subst P p pbase ≡ pbase) (loopⁿ 2) (refl pbase) ≡ refl pbase)
    test₂ _ _ = refl _

private
  cong-,, : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {x y : A} (p : x ≡ y)
           {x₁ : B x} {y₁ : B y} (p₁ : subst B p x₁ ≡ y₁)
           {x₂ : B x} {y₂ : B y} (p₂ : subst B p x₂ ≡ y₂) →
           (x , x₁ , x₂) ≡ (y , y₁ , y₂)
  cong-,, B = elim
              (λ {x y} (p : x ≡ y) →
                  ∀ {x₁} {y₁} (p₁ : subst B p x₁ ≡ y₁)
                  {x₂} {y₂} (p₂ : subst B p x₂ ≡ y₂) →
                  (x , x₁ , x₂) ≡ (y , y₁ , y₂))
              (λ x p₁ p₂ → cong₂ (λ x₁ x₂ → (x , x₁ , x₂)) p₁ p₂)

  subst-cong-,, : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {x y : A} (p : x ≡ y)
                  {x₁₂ : B x} {y₁₂ : B y} (p₁₂ : subst B p x₁₂ ≡ y₁₂) →
                  subst (λ s → proj₁ (proj₂ s) ≡ proj₂ (proj₂ s)) (cong-,, B p p₁₂ p₁₂) (refl x₁₂) ≡ refl y₁₂
  subst-cong-,, B = elim
              (λ {x y} p →
                  {x₁₂ : B x} {y₁₂ : B y} (p₁₂ : subst B p x₁₂ ≡ y₁₂) →
                  subst (λ s → proj₁ (proj₂ s) ≡ proj₂ (proj₂ s)) (cong-,, B p p₁₂ p₁₂) (refl x₁₂) ≡ refl y₁₂)
              (λ x → elim
                  (λ {x₁₂ y₁₂} p₁₂ →
                      subst (λ s → proj₁ (proj₂ s) ≡ proj₂ (proj₂ s)) (cong-,, B (refl x) p₁₂ p₁₂) (refl x₁₂) ≡ refl y₁₂)
                  (λ x₁₂ → refl _))

  lemma₁ : ∀ {ℓ} m {S} (P : S → Set ℓ) (f : (x : S) → P x) (b : S) →
           cong-endpoints[dep]⇑ m P f (S-endpoints⇑ m b) ≡ S-endpoints[dep]⇑ m P b (f b)
  lemma₂ : ∀ {ℓ} m {S} (P : S → Set ℓ) (f : (x : S) → P x) (b : S) →
           subst (Path[dep]⇑ m P (S-loop⇑ m b)) (lemma₁ m P f b)
              (cong[dep]⇑ m P f (S-endpoints⇑ m b) (S-loop⇑ m b)) ≡
           S-loop[dep]⇑ m P b (f b)
  
  lemma₁ 0       _ _ _ = refl _
  lemma₁ (suc m) P f b = cong-,, (Path[dep]⇑ m P (S-loop⇑ m b)) (lemma₁ m P f b) (lemma₂ m P f b) (lemma₂ m P f b)
  
  lemma₂ 0       _ _ _ = refl _
  lemma₂ (suc m) P f b = subst-cong-,, (Path[dep]⇑ m P (S-loop⇑ m b)) (lemma₁ m P f b) (lemma₂ m P f b)

  lemma-main : ∀ {ℓ} n (P : Sⁿ n → Set ℓ) (pbase : P (baseⁿ n)) (ploop : Path[dep]⇑ n P (loopⁿ n) (Sⁿ-endpoints[dep] n P pbase)) →
               cong-endpoints[dep]⇑ n P (Sⁿ-elim n P pbase ploop) (Sⁿ-endpoints n) ≡ Sⁿ-endpoints[dep] n P pbase
  lemma-main n P pbase ploop = lemma₁ n P (Sⁿ-elim n P pbase ploop) (baseⁿ n)

private
  -- Some test cases for the type of "lemma-main"
  module Test₃ where
    test₀ : ∀ {ℓ} (P : Sⁿ 0 → Set ℓ) (pbase : P (baseⁿ 0)) (ploop : Path[dep]⇑ 0 P (loopⁿ 0) (Sⁿ-endpoints[dep] 0 P pbase)) →
            lemma-main 0 P pbase ploop ≡ refl _
    test₀ _ _ _ = refl _

    test₁ : ∀ {ℓ} (P : Sⁿ 1 → Set ℓ) (pbase : P (baseⁿ 1)) (ploop : Path[dep]⇑ 1 P (loopⁿ 1) (Sⁿ-endpoints[dep] 1 P pbase)) →
            lemma-main 1 P pbase ploop ≡ refl _
    test₁ _ _ _ = refl _

    test₂ : ∀ {ℓ} (P : Sⁿ 2 → Set ℓ) (pbase : P (baseⁿ 2)) (ploop : Path[dep]⇑ 2 P (loopⁿ 2) (Sⁿ-endpoints[dep] 2 P pbase)) →
            lemma-main 2 P pbase ploop ≡ refl _
    test₂ _ _ _ = refl _

    test₁₀ : ∀ {ℓ} (P : Sⁿ 10 → Set ℓ) (pbase : P (baseⁿ 10)) (ploop : Path[dep]⇑ 10 P (loopⁿ 10) (Sⁿ-endpoints[dep] 10 P pbase)) →
             lemma-main 10 P pbase ploop ≡ refl _
    test₁₀ _ _ _ = refl _

postulate
  Sⁿ-elim-loop : ∀ {ℓ} n (P : Sⁿ n → Set ℓ) (pbase : P (baseⁿ n)) (ploop : Path[dep]⇑ n P (loopⁿ n) (Sⁿ-endpoints[dep] n P pbase)) →
                 subst (Path[dep]⇑ n P (loopⁿ n)) (lemma-main n P pbase ploop)
                    (cong[dep]⇑ n P (Sⁿ-elim n P pbase ploop) (Sⁿ-endpoints n) (loopⁿ n)) ≡
                 ploop

private
  -- Some test cases for the type of the LHS of "Sⁿ-elim-loop"
  module Test₄ where
    test₀ : ∀ {ℓ} (P : Sⁿ 0 → Set ℓ) (pbase : P (baseⁿ 0)) (ploop : Path[dep]⇑ 0 P (loopⁿ 0) (Sⁿ-endpoints[dep] 0 P pbase)) →
            subst (Path[dep]⇑ 0 P (loopⁿ 0)) (lemma-main 0 P pbase ploop)
                (cong[dep]⇑ 0 P (Sⁿ-elim 0 P pbase ploop) (Sⁿ-endpoints 0) (loopⁿ 0))
            ≡ (Sⁿ-elim 0 P pbase ploop) (loopⁿ 0)
    test₀ _ _ _ = refl _

    test₁ : ∀ {ℓ} (P : Sⁿ 1 → Set ℓ) (pbase : P (baseⁿ 1)) (ploop : Path[dep]⇑ 1 P (loopⁿ 1) (Sⁿ-endpoints[dep] 1 P pbase)) →
            subst (Path[dep]⇑ 1 P (loopⁿ 1)) (lemma-main 1 P pbase ploop)
                (cong[dep]⇑ 1 P (Sⁿ-elim 1 P pbase ploop) (Sⁿ-endpoints 1) (loopⁿ 1))
            ≡ cong[dep] P (Sⁿ-elim 1 P pbase ploop) (loopⁿ 1)
    test₁ _ _ _ = refl _

    test₂ : ∀ {ℓ} (P : Sⁿ 2 → Set ℓ) (pbase : P (baseⁿ 2)) (ploop : Path[dep]⇑ 2 P (loopⁿ 2) (Sⁿ-endpoints[dep] 2 P pbase)) →
            subst (Path[dep]⇑ 2 P (loopⁿ 2)) (lemma-main 2 P pbase ploop)
                (cong[dep]⇑ 2 P (Sⁿ-elim 2 P pbase ploop) (Sⁿ-endpoints 2) (loopⁿ 2))
            ≡ cong[dep] (λ p → subst P p pbase ≡ pbase) (cong[dep] P (Sⁿ-elim 2 P pbase ploop)) (loopⁿ 2)
    test₂ _ _ _ = refl _

{-
-- TODO Non-dependent version for Sⁿ

S²-elim[simp] : ∀ {ℓ} {P : Set ℓ} (pbase : P) → refl pbase ≡ refl pbase → S² → P
S²-elim[simp] {P = P} pbase ploop = S²-elim (const P) pbase (trans boring-loop ploop)
  where
    boring-loop = cong[dep] (λ p → subst (const P) p pbase ≡ pbase) (λ p → subst-const p pbase) loop²

-- TODO This rule should be derivable from the dependent one
postulate
  S²-elim[simp]-loop : ∀ {ℓ} {P : Set ℓ} (pbase : P) (ploop : refl pbase ≡ refl pbase)
                       → cong (cong (S²-elim[simp] pbase ploop)) loop² ≡ ploop
-}
