------------------------------------------------------------------------
-- Higher-order paths and loops
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

module Path.Higher-order where

open import Prelude
open import Path
open import Path.Lemmas

-- TODO Generic boring paths for the case that B is a constant function.
-- TODO Build a nicer interface for Env. (Although the hidden definition
--      the one suitable for induction...) Make sure definitional equalities
--      hold for all finite cases.

------------------------------------------------------------------------
-- Higher-order loop spaces

Ω : ∀ {ℓ} n {A : Set ℓ} → A → Set ℓ
Ω-refl : ∀ {ℓ} n {A : Set ℓ} (base : A) → Ω n base

Ω 0       {A} _    = A
Ω (suc n) {A} base = Ω-refl n base ≡ Ω-refl n base

Ω-refl 0       base = base
Ω-refl (suc n) base = refl (Ω-refl n base)

------------------------------------------------------------------------
-- Higher-order path spaces

-- This definition is not suitable for inductive definition of cong[dep]⇑
--Paths⇑ : ∀ {ℓ} n → Set ℓ → Set ℓ
--Paths⇑ 0       A = A
--Paths⇑ (suc i) A = Σ A (λ x → Σ A (λ y → Paths⇑ i (x ≡ y)))

-- Env 0 = tt
-- Env 1 = (tt , (x₁ , y₁))
-- Env 2 = ((tt , (x₁ , y₁)) , (x₂ , y₂))
-- Env 3 = (((tt , (x₁ , y₁)) , (x₂ , y₂)) , (x₃ , y₃))
private
  Env⇑ : ∀ {ℓ} n → Set ℓ → Set ℓ
  Path⇑ : ∀ {ℓ} n (A : Set ℓ) → Env⇑ n A → Set ℓ

  Env⇑ {ℓ} 0             A = ↑ ℓ ⊤
  Env⇑ {ℓ} 1             A = A × A
  Env⇑     (suc (suc i)) A = Σ (Env⇑ i A) (λ e → Path⇑ i A e × Path⇑ i A e)

  Path⇑ 0             A _             = A
  Path⇑ 1             A (x , y)       = x ≡ y
  Path⇑ (suc (suc i)) A (_ , (x , y)) = x ≡ y

--usable but useless
--Paths⇑ : ∀ {ℓ} n → Set ℓ → Set ℓ
--Paths⇑ n A = Σ (Env⇑ n A) (Path⇑ n A)

-- These interfaces will be changed
Cong[dep]-env⇑ : ∀ {ℓ} n → Set ℓ → Set ℓ
Cong[dep]-env⇑ = Env⇑

Cong[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
             (e : Env⇑ n A) (p : Path⇑ n A e) → Set ℓ₂
cong[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
             (e : Env⇑ n A) (p : Path⇑ n A e) → Cong[dep]⇑ n B f _ p

Cong[dep]⇑ 0             B f _             p = B p
Cong[dep]⇑ 1             B f (x , y)       p = subst B p (f x) ≡ (f y)
Cong[dep]⇑ (suc (suc i)) B f (_ , (x , y)) p = subst (Cong[dep]⇑ i B f _) p (cong[dep]⇑ i B f _ x) ≡ cong[dep]⇑ i B f _ y

cong[dep]⇑ 0             B f _             p = f p
cong[dep]⇑ 1             B f (x , y)       p = cong[dep] B f p
cong[dep]⇑ (suc (suc i)) B f (_ , (x , y)) p = cong[dep] (Cong[dep]⇑ i B f _) (cong[dep]⇑ i B f _) p

-- Env 0 = tt
-- Env 1 = (tt , ((ax₁ , bx₁) , (ay₁ , by₁)))
-- Env 2 = ((tt , ((ax₁ , bx₁) , (ay₁ , by₂))) , ((ax₂ , bx₂) , (ay₂ , by₂)))
private
  Env[d]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
  PathA[d]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) → Env[d]⇑ n B → Set ℓ₁
  PathB[d]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) (e : Env[d]⇑ n B) → PathA[d]⇑ n B e → Set ℓ₂

  Env[d]⇑ {ℓ₁} {ℓ₂} 0       B = ↑ (ℓ₁ ⊔ ℓ₂) ⊤
  Env[d]⇑           (suc i) B = Σ (Env[d]⇑ i B) (λ e → Σ (PathA[d]⇑ i B e) (PathB[d]⇑ i B e) ×
                                                       Σ (PathA[d]⇑ i B e) (PathB[d]⇑ i B e))

  PathA[d]⇑ 0       {A} _ _                           = A
  PathA[d]⇑ (suc i)     _ (_ , ((ax , _) , (ay , _))) = ax ≡ ay

  PathB[d]⇑ 0       B _                           a = B a
  PathB[d]⇑ (suc i) B (_ , ((_ , bx) , (_ , by))) a = subst (PathB[d]⇑ i B _) a bx ≡ by

-- This interface will be changed
PathB[dep]⇑-env : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
PathB[dep]⇑-env = Env[d]⇑

-- This interface will be changed
PathB[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) (e : Env[d]⇑ n B) → PathA[d]⇑ n B e → Set ℓ₂
PathB[dep]⇑ = PathB[d]⇑

