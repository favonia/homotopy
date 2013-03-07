------------------------------------------------------------------------
-- Higher-order paths and loops
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

module Path.HigherOrder where

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
endpoints′⇒endpoints⇑ : ∀ {ℓ} n m {A : Set ℓ} (eA : Endpoints⇑ n A) → Endpoints′⇑ m (Path⇑ n eA) → Endpoints⇑ (m + n) A
endpoints′⇒endpoints⇑ n 0           c _           = c
endpoints′⇒endpoints⇑ n (suc m) {A} c (x , y , p) =
    subst (λ n → Endpoints⇑ n A) (n+suc m n) $ endpoints′⇒endpoints⇑ (suc n) m (_ , (x , y)) p

-- A section that parametrized by a high-order path
-- Endpoints[d] 0 = tt
-- Endpoints[d] 1 = (tt, bx₁ , by₁)
-- Endpoints[d] 2 = ((tt, bx₁ , by₂) , bx₂ , by₂)
Endpoints[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) → Endpoints⇑ n A → Set ℓ₂
Path[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) {eA : Endpoints⇑ n A} → Path⇑ n eA → Endpoints[dep]⇑ n B eA → Set ℓ₂

Endpoints[dep]⇑ {ℓ₁} {ℓ₂} 0       _ _            = ↑ ℓ₂ ⊤
Endpoints[dep]⇑           (suc n) B (eA , x , y) = Σ (Endpoints[dep]⇑ n B eA)
                                                     (λ c → Path[dep]⇑ n B x c × Path[dep]⇑ n B y c)

Path[dep]⇑ 0       B a _              = B a
Path[dep]⇑ (suc n) B a (eB , bx , by) = subst (λ x → Path[dep]⇑ n B x eB) a bx ≡ by

------------------------------------------------------------------------
-- cong (resp, map) for higher-order path

-- Higher-order cong(ruence) that takes high-order paths
-- Reuse Path[dep] to avoid all sorts of problems in Space.Sphere
cong-endpoints[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
                       (eA : Endpoints⇑ n A) → Endpoints[dep]⇑ n B eA
cong[dep]⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} (B : A → Set ℓ₂) (f : (x : A) → B x)
             (eA : Endpoints⇑ n A) (pA : Path⇑ n eA) → Path[dep]⇑ n B pA (cong-endpoints[dep]⇑ n B f eA)

cong-endpoints[dep]⇑ 0       B f _            = lift tt
cong-endpoints[dep]⇑ (suc n) B f (eA , x , y) = (cong-endpoints[dep]⇑ n B f eA ,
                                                 cong[dep]⇑ n B f eA x ,
                                                 cong[dep]⇑ n B f eA y)

cong[dep]⇑ 0       B f t              p = f p
cong[dep]⇑ (suc n) B f (eA , (x , y)) p = cong[dep] (λ x → Path[dep]⇑ n B x (cong-endpoints[dep]⇑ n B f eA)) (cong[dep]⇑ n B f eA) p

-- Higher-order non-dependent cong(ruence) that takes high-order paths
cong-endpoints⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B)
                  (eA : Endpoints⇑ n A) → Endpoints⇑ n B
cong⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B)
        (eA : Endpoints⇑ n A) (pA : Path⇑ n eA) → Path⇑ n (cong-endpoints⇑ n f eA)

cong-endpoints⇑ 0       f _            = lift tt
cong-endpoints⇑ (suc n) f (eA , x , y) = (cong-endpoints⇑ n f eA ,
                                          cong⇑ n f eA x ,
                                          cong⇑ n f eA y)

cong⇑ 0       f t              p = f p
cong⇑ (suc n) f (eA , (x , y)) p = cong (cong⇑ n f eA) p

-- Generalized cong[dep]-const

cong-endpoints[dep]-const⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (eA : Endpoints⇑ n A) (pA : Path⇑ n eA) → 
                             Path[dep]⇑ n (const B) pA (cong-endpoints[dep]⇑ n (const B) f eA) ≡ Path⇑ n (cong-endpoints⇑ n f eA)

cong[dep]-const⇑ : ∀ {ℓ₁ ℓ₂} n {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (eA : Endpoints⇑ n A) (pA : Path⇑ n eA) → 
                  subst id (cong-endpoints[dep]-const⇑ n f eA pA) (cong[dep]⇑ n (const B) f eA pA) ≡ cong⇑ n f eA pA

cong-endpoints[dep]-const⇑ 0               _ _            _  = refl _
cong-endpoints[dep]-const⇑ (suc n) {B = B} f (eA , x , y) pA = elim
    (λ {x y} pA →
        Path[dep]⇑ (suc n) (const B) pA (cong-endpoints[dep]⇑ (suc n) (const B) f (eA , x , y)) ≡
        Path⇑ (suc n) (cong-endpoints⇑ (suc n) f (eA , x , y)))
    (λ x → cong-≡ (cong-endpoints[dep]-const⇑ n f eA x) (cong[dep]-const⇑ n f eA x) (cong[dep]-const⇑ n f eA x))
    pA

cong[dep]-const⇑ 0               _ _            _  = refl _
cong[dep]-const⇑ (suc n) {B = B} f (eA , x , y) pA = elim
    (λ {x y} pA →
        subst id (cong-endpoints[dep]-const⇑ (suc n) f (eA , x , y) pA) (cong[dep]⇑ (suc n) (const B) f (eA , x , y) pA) ≡
        cong⇑ (suc n) f (eA , x , y) pA)
    (λ x → subst-cong-≡ (cong-endpoints[dep]-const⇑ n f eA x) (cong[dep]-const⇑ n f eA x))
    pA
