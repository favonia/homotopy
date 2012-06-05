module Space.Flower where

open import Prelude

open import Path
open import Path.Lemmas

private
  data Flower′ (n : ℕ) : Set where
    core : Flower′ n

Flower : ℕ → Set
Flower n = Flower′ n

-- Dependent version

postulate
  petal : ∀ {n} → Fin n → _≡_ {A = Flower n} core core

Flower-elim : ∀ {ℓ} {n} (P : Flower n → Set ℓ)
                (pcore : P core)
                (ppetal : ∀ i → subst P (petal i) pcore ≡ pcore) →
              ∀ f → P f
Flower-elim _ pcore _ core = pcore

postulate
  Flower-elim-petal : ∀ {ℓ} {n} (P : Flower n → Set ℓ)
                        (pcore : P core)
                        (ppetal : ∀ i → subst P (petal i) pcore ≡ pcore) →
                      ∀ i → cong[dep] P (Flower-elim P pcore ppetal) (petal i) ≡ ppetal i

-- Non-dependent version

Flower-elim[simp] : ∀ {ℓ} {n} {P : Set ℓ}
                      (pcore : P) (ppetal : ∀ (i : Fin n) → pcore ≡ pcore) →
                    ∀ f → P
Flower-elim[simp] {n = n} {P = P} pcore ppetal =
  Flower-elim (const P) pcore (λ i → trans (boring-petal i) (ppetal i))
  where
    boring-petal : ∀ (i : Fin n) → subst (const P) (petal i) pcore ≡ pcore
    boring-petal i = subst-const (petal i) pcore

-- This propositional equality is derivable from the dependent version.
Flower-elim[simp]-petal : ∀ {ℓ} {n} {P : Set ℓ}
                            (pcore : P)
                            (ppetal : ∀ (i : Fin n) → pcore ≡ pcore) →
                          ∀ i → cong (Flower-elim[simp] pcore ppetal) (petal i) ≡ ppetal i
Flower-elim[simp]-petal {n = n} {P = P} pcore ppetal i =
  cong pflower (petal i)
    ≡⟨ sym $ trans-sym-trans (boring-petal i) _ ⟩
  trans (sym $ boring-petal i) (trans (boring-petal i) $ cong pflower $ petal i)
    ≡⟨ cong (trans $ sym $ boring-petal i) $ sym $ cong[dep]-const pflower (petal i) ⟩
  trans (sym $ boring-petal i) (cong[dep] (const P) pflower $ petal i)
    ≡⟨ cong (trans $ sym $ boring-petal i) $ Flower-elim-petal (const P) _ _ i ⟩
  trans (sym $ boring-petal i) (trans (boring-petal i) $ ppetal i)
    ≡⟨ trans-sym-trans (boring-petal i) _ ⟩∎
  ppetal i
    ∎
  where
    boring-petal : ∀ (i : Fin n) → subst (const P) (petal i) pcore ≡ pcore
    boring-petal i = subst-const (petal i) pcore

    pflower = Flower-elim[simp] pcore ppetal
