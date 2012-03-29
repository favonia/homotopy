------------------------------------------------------------------------
-- Higher-order paths and loops
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

module Path.Higher-order where

open import Prelude
open import Path
open import Path.Lemmas
open import Space.Nat.Lemmas

-- TODO Generalized cong[dep]-const lemma

------------------------------------------------------------------------
-- Higher-order loop spaces

Ω : ∀ {ℓ} n {A : Set ℓ} → A → Set ℓ
private Ω-refl : ∀ {ℓ} n {A : Set ℓ} (base : A) → Ω n base

Ω 0       {A} _    = A
Ω (suc n) {A} base = Ω-refl n base ≡ Ω-refl n base

Ω-refl 0       base = base
Ω-refl (suc n) base = refl (Ω-refl n base)

------------------------------------------------------------------------
-- Higher-order path spaces

-- Endpoints[d] 0 = tt
-- Endpoints[d] 1 = (tt, x₁ , y₁)
-- Endpoints[d] 2 = ((tt, x₁ , y₂) , x₂ , y₂)

-- This definition is perfect for induction but probably not user-friendly
Endpoints⇑ : ∀ {ℓ} n → Set ℓ → Set ℓ
Path⇑ : ∀ {ℓ} n {A : Set ℓ} → Endpoints⇑ n A → Set ℓ

Endpoints⇑ {ℓ} 0       A = ↑ ℓ ⊤
Endpoints⇑     (suc n) A = Σ (Endpoints⇑ n A) (λ c → Path⇑ n c × Path⇑ n c)

Path⇑ 0       {A} _           = A
Path⇑ (suc n)     (_ , x , y) = x ≡ y

-- This definition is terrible for induction, but seems nicer to use?
Endpoints′⇑ : ∀ {ℓ} n → Set ℓ → Set ℓ
Endpoints′⇑ {ℓ} 0       A = ↑ ℓ ⊤
Endpoints′⇑     (suc n) A = Σ A (λ x → Σ A ( λ y → Endpoints′⇑ n (x ≡ y)))

-- A helper function to convert the above definition
endpoints′⇒endpoints⇑ : ∀ {ℓ} n m {A : Set ℓ} (cA : Endpoints⇑ n A) → Endpoints′⇑ m (Path⇑ n cA) → Endpoints⇑ (m + n) A
endpoints′⇒endpoints⇑ n 0           c _           = c
endpoints′⇒endpoints⇑ n (suc m) {A} c (x , y , p) =
    subst (λ n → Endpoints⇑ n A) (n+suc m n) $ endpoints′⇒endpoints⇑ (suc n) m (_ , (x , y)) p

-- A section that parametrized by a high-order path
-- Endpoints[d] 0 = tt
-- Endpoints[d] 1 = (tt, bx₁ , by₁)
-- Endpoints[d] 2 = ((tt, bx₁ , by₂) , bx₂ , by₂)
Endpoints[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) → Endpoints⇑ n A → Set ℓ₂
Path[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) {cA : Endpoints⇑ n A} → Path⇑ n cA → Endpoints[dep]⇑ n B cA → Set ℓ₂

Endpoints[dep]⇑ {ℓ₁} {ℓ₂} 0       _ _            = ↑ ℓ₂ ⊤
Endpoints[dep]⇑           (suc n) B (cA , x , y) = Σ (Endpoints[dep]⇑ n B cA)
                                                    (λ c → Path[dep]⇑ n B x c × Path[dep]⇑ n B y c)

Path[dep]⇑ 0       B a _              = B a
Path[dep]⇑ (suc n) B a (cB , bx , by) = subst (λ x → Path[dep]⇑ n B x cB) a bx ≡ by

-- Higher-order cong(ruence) that takes high-order paths
-- Reuse Path[dep] to avoid all sorts of problems in Space.Sphere
cong-endpoints[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
                       (cA : Endpoints⇑ n A) → Endpoints[dep]⇑ n B cA
cong[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
             (cA : Endpoints⇑ n A) (pA : Path⇑ n cA) → Path[dep]⇑ n B pA (cong-endpoints[dep]⇑ n B f cA)

cong-endpoints[dep]⇑ 0       B f _            = lift tt
cong-endpoints[dep]⇑ (suc n) B f (cA , x , y) = (cong-endpoints[dep]⇑ n B f cA ,
                                                 cong[dep]⇑ n B f cA x ,
                                                 cong[dep]⇑ n B f cA y)

cong[dep]⇑ 0       B f t              p = f p
cong[dep]⇑ (suc n) B f (cA , (x , y)) p = cong[dep] (λ x → Path[dep]⇑ n B x (cong-endpoints[dep]⇑ n B f cA)) (cong[dep]⇑ n B f cA) p

