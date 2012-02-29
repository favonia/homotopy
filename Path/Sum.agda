------------------------------------------------------------------------
-- Paths in Σ types
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

-- The public interface includes
--  * A bijection between (a₁ , b₁) ≡ (a₂ , b₂)
--    and Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)

module Path.Sum where
 
open import Prelude
open import Path
open import Path.Lemmas
open import Bijection hiding (id; _∘_; inverse)

------------------------------------------------------------------------
-- A bijection between ((a₁ , b₁) ≡ (a₂ , b₂)) and
-- Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)

-- Compose equalities in a Σ type

Σ≡⇒≡Σ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
        Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) → (a₁ , b₁) ≡ (a₂ , b₂)
Σ≡⇒≡Σ B {a₁} {a₂} {b₁} {b₂} (a≡a , b≡b) = elim
  (λ {a₁ a₂} a≡a → ∀ {b₁ : B a₁} {b₂ : B a₂} → subst B a≡a b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂))
  (λ a → λ {b₁} {b₂} b≡b →
    (a , b₁)                  ≡⟨ refl _ ⟩
    (a , subst B (refl a) b₁) ≡⟨ cong (λ b → (a , b)) b≡b ⟩∎
    (a , b₂)                  ∎)
  a≡a b≡b

-- Decompose equalities for a Σ type

≡Σ⇒Σ≡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
        (a₁ , b₁) ≡ (a₂ , b₂) → Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)
≡Σ⇒Σ≡ {A = A} B {b₁ = b₁} {b₂ = b₂} s≡s = (a≡a , b≡b)
  where
    a≡a = cong proj₁ s≡s
    b≡b =
      subst B a≡a b₁            ≡⟨ subst-cong B proj₁ s≡s b₁ ⟩
      subst (B ∘ proj₁) s≡s b₁  ≡⟨ cong[dep] (B ∘ proj₁) proj₂ s≡s ⟩∎
      b₂                        ∎

------------------------------------------------------------------------
-- Composition and decomposition form a bijection!

≡Σ↔Σ≡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
          ((a₁ , b₁) ≡ (a₂ , b₂)) ↔ Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)
≡Σ↔Σ≡ B {a₁} {a₂} {b₁} {b₂} =
  record
  { surjection = record
    { equivalence = record
      { to = ≡Σ⇒Σ≡ B
      ; from = Σ≡⇒≡Σ B
      }
    ; right-inverse-of = right-inverse-of
    }
  ; left-inverse-of = left-inverse-of
  }
  where
    left-inverse-of : (p : (a₁ , b₁) ≡ (a₂ , b₂)) → Σ≡⇒≡Σ B (≡Σ⇒Σ≡ B p) ≡ p
    left-inverse-of p =
      elim
        (λ {s₁ s₂} p → Σ≡⇒≡Σ B (≡Σ⇒Σ≡ B p) ≡ p)
        (λ s → refl _)
        p

    right-inverse-of : (s : Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)) → ≡Σ⇒Σ≡ B (Σ≡⇒≡Σ B s) ≡ s
    right-inverse-of (pa , pb) =
      elim
        (λ {a₁ a₂} pa → {b₁ : B a₁} {b₂ : B a₂} (pb : subst B pa b₁ ≡ b₂) → ≡Σ⇒Σ≡ B (Σ≡⇒≡Σ B (pa , pb)) ≡ (pa , pb))
        (λ a →
          elim 
          (λ {b₁ : B a} {b₂ : B a} (pb : b₁ ≡ b₂) → ≡Σ⇒Σ≡ B (Σ≡⇒≡Σ B (refl a , pb)) ≡ (refl a , pb))
          (λ b → refl _))
        pa pb

------------------------------------------------------------------------
-- Other lemmas for paths in Σ

private
  Cong-Σ≡⇒≡Σ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} (B : A → Set ℓ₂) (C : Set ℓ₃)
               (f : (x : A) → B x → C) {a₁ a₂ : A} (p : a₁ ≡ a₂) {b₁ : B a₁} {b₂ : B a₂} (q : subst B p b₁ ≡ b₂) →
               Set ℓ₃
  Cong-Σ≡⇒≡Σ B C f {a₁} {a₂} p {b₁} {b₂} q =
            cong (uncurry f) (Σ≡⇒≡Σ B (p , q)) ≡
            (f a₁ b₁                                         ≡⟨ sym $ subst-const p (f a₁ b₁) ⟩
             subst (const C) p (f a₁ b₁)                     ≡⟨ subst-app B (const C) p (f a₁) q ⟩
             subst (λ x → B x → C) p (f a₁) b₂               ≡⟨ cong (λ f′ → f′ b₂) $ cong[dep] (λ x → B x → C) f p ⟩∎
             f a₂ b₂                                         ∎)

cong-Σ≡⇒≡Σ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} (B : A → Set ℓ₂) (C : Set ℓ₃)
          (f : (x : A) → B x → C) {a₁ a₂ : A} (p : a₁ ≡ a₂) {b₁ : B a₁} {b₂ : B a₂} (q : subst B p b₁ ≡ b₂) →
          Cong-Σ≡⇒≡Σ B C f p q

cong-Σ≡⇒≡Σ B C f =
  elim
    (λ {a₁ a₂} p → {b₁ : B a₁} {b₂ : B a₂} (q : subst B p b₁ ≡ b₂) → Cong-Σ≡⇒≡Σ B C f p q)
    (λ a →
        elim
          (λ {b₁ b₂} q → Cong-Σ≡⇒≡Σ B C f (refl a) q)
          (λ b → refl _))

private
  Subst-Σfunc : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} (B : A → Set ℓ₂) (C : Σ A B → Set ℓ₃)
                {a₁ a₂ : A} (p : a₁ ≡ a₂) (f₁ : (b₁ : B a₁) → C (a₁ , b₁))
                {b₁ : B a₁} {b₂ : B a₂} (q : subst B p b₁ ≡ b₂) → Set ℓ₃
  Subst-Σfunc B C p f₁ {b₁} {b₂} q =
                subst (λ a → (b : B a) → C (a , b)) p f₁ b₂ ≡
                subst C (Σ≡⇒≡Σ B (p , q)) (f₁ b₁)

subst-Σfunc : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} (B : A → Set ℓ₂) (C : Σ A B → Set ℓ₃)
              {a₁ a₂ : A} (p : a₁ ≡ a₂) (f₁ : (b₁ : B a₁) → C (a₁ , b₁))
              {b₁ : B a₁} {b₂ : B a₂} (q : subst B p b₁ ≡ b₂) → Subst-Σfunc B C p f₁ q
subst-Σfunc B C =
  elim
    (λ {a₁ a₂} p → ∀ f₁ {b₁ : B a₁} {b₂ : B a₂} q → Subst-Σfunc B C p f₁ q)
    (λ a f₁ → elim
        (λ {b₁} {b₂} q → Subst-Σfunc B C (refl a) f₁ q)
        (λ b → refl _))

