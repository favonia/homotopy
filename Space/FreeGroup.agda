------------------------------------------------------------------------
-- Free groups
------------------------------------------------------------------------

-- Copyright (c) 2012 Favonia

{-# OPTIONS --without-K #-}

module Space.FreeGroup where

open import Prelude

open import Path
open import Path.Lemmas

open import Space.Fin.Lemmas as F
open import Space.List.Lemmas as L

-- ... was Alphabet n = Fin n ⊎ Fin n before
data Alphabet (n : ℕ) : Set where
  gen : Fin n → Alphabet n
  inv : Fin n → Alphabet n

Word : ℕ → Set
Word n = List (Alphabet n)

data isUnstable {n : ℕ} : Alphabet n → Alphabet n → Set where
  gen-inv : ∀ (x : Fin n) → isUnstable (gen x) (inv x)
  inv-gen : ∀ (x : Fin n) → isUnstable (inv x) (gen x)

isStable : ∀ {n} → Alphabet n → Alphabet n → Set
isStable x y = ¬ isUnstable x y

data isReducible {n} : Word n → Set where
  boom : ∀ {x₁ x₂ : Alphabet n} → isUnstable x₁ x₂ → (xs : Word n) → isReducible (x₁ ∷ x₂ ∷ xs)
  skip : ∀ (x : Alphabet n) {xs : Word n} → isReducible xs → isReducible (x ∷ xs)

isNormalized : ∀ {n} → Word n → Set
isNormalized w = ¬ isReducible w

decideUnstable : ∀ {n} (x : Alphabet n) (y : Alphabet n) → Dec (isUnstable x y)
decideUnstable (gen x) (gen y) = inj₂ λ{()}
decideUnstable (inv x) (inv y) = inj₂ λ{()}
decideUnstable {n} (gen x) (inv y) with F.decide-≡ x y
...                                | inj₁ eq = inj₁ $ subst (isUnstable (gen x)) (cong inv eq) (gen-inv x)
...                                | inj₂ neq = inj₂ $ neq ∘ inversion
  where
    inversion : ∀ {x y : Fin n} → isUnstable (gen x) (inv y) → x ≡ y
    inversion (gen-inv _) = refl _
decideUnstable {n} (inv x) (gen y) with F.decide-≡ x y
...                                | inj₁ eq = inj₁ $ subst (isUnstable (inv x)) (cong gen eq) (inv-gen x)
...                                | inj₂ neq = inj₂ $ neq ∘ inversion
  where
    inversion : ∀ {x y : Fin n} → isUnstable (inv x) (gen y) → x ≡ y
    inversion (inv-gen _) = refl _

Free : ℕ → Set
Free n = Σ (Word n) isNormalized

private
  cons-stable : ∀ {n} {a₁ a₂ : Alphabet n} {w : Word n} → isStable a₁ a₂ → isNormalized (a₂ ∷ w) → isNormalized (a₁ ∷ a₂ ∷ w)
  cons-stable stable norm (skip _ red) = norm red
  cons-stable stable norm (boom u _) = stable u

  rev-word-prepend : ∀ {n} → Word n → Free n → Free n
  rev-word-prepend []       f             = f
  rev-word-prepend (x ∷ xs) ([] , _)      = rev-word-prepend xs (x ∷ [] , λ{(skip .x ())})
  rev-word-prepend (x ∷ xs) (y ∷ ys , n) with decideUnstable x y
  ...                                    | inj₁ unstable = rev-word-prepend xs (ys , n ∘ skip y)
  ...                                    | inj₂ stable   = rev-word-prepend xs (x ∷ y ∷ ys , λ{(boom u .ys) → stable u; (skip .x r) → n r})

  word-prepend : ∀ {n} → Word n → Free n → Free n
  word-prepend w f = rev-word-prepend (rev w) f

  free-concat : ∀ {n} → Free n → Free n → Free n
  free-concat (w₁ , _) f₂ = word-prepend w₁ f₂

  word-flip : ∀ {n} → Word n → Word n
  word-flip [] = []
  word-flip (gen x ∷ xs) = inv x ∷ word-flip xs
  word-flip (inv x ∷ xs) = gen x ∷ word-flip xs

  word-flip-flip : ∀ {n} (w : Word n) → word-flip (word-flip w) ≡ w
  word-flip-flip [] = refl _
  word-flip-flip (gen x ∷ xs) = cong (λ xs → gen x ∷ xs) $ word-flip-flip xs
  word-flip-flip (inv x ∷ xs) = cong (λ xs → inv x ∷ xs) $ word-flip-flip xs

  -- Q: Is it possible to prove
  --   ∀ {n} (w : Word n) → isNormalized w → isNormalized (word-flip w)
  -- directly? Agda is unhappy when I tried to pattern match against
  --   isNormalized (word-flip w)
  norm-flip′ : ∀ {n} (w : Word n) → isNormalized (word-flip w) → isNormalized w
  norm-flip′ []                    n ()
  norm-flip′ (inv x ∷ xs)          n (skip .(inv x) rs) = norm-flip′ xs (n ∘ skip (gen x)) rs
  norm-flip′ (gen x ∷ xs)          n (skip .(gen x) rs) = norm-flip′ xs (n ∘ skip (inv x)) rs
  norm-flip′ (gen x ∷ inv .x ∷ xs) n (boom (gen-inv .x) .xs) = n $ boom (inv-gen x) (word-flip xs)
  norm-flip′ (inv x ∷ gen .x ∷ xs) n (boom (inv-gen .x) .xs) = n $ boom (gen-inv x) (word-flip xs)
  norm-flip′ (gen _ ∷ gen _ ∷ xs)  n (boom () .xs)
  norm-flip′ (inv _ ∷ inv _ ∷ xs)  n (boom () .xs)

  norm-flip : ∀ {n} (w : Word n) → isNormalized w → isNormalized (word-flip w)
  norm-flip w n = norm-flip′ (word-flip w) $ subst isNormalized (sym $ word-flip-flip w) n

  free-flip : ∀ {n} → Free n → Free n
  free-flip (w , n) = (word-flip w , norm-flip w n)

  free-rev : ∀ {n} → Free n → Free n
  free-rev (w , n) = rev-word-prepend w ([] , λ{()})

  -- TODO correctness of free-rev 
