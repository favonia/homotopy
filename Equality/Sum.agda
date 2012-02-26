------------------------------------------------------------------------
-- Lemmas for equalities in Σ types
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- The public interface includes
--  * A bijection between (a₁ , b₁) ≡ (a₂ , b₂)
--    and Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)

open import Prelude
open import Equality

module Equality.Sum
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where
 
open Derived-definitions-and-properties eq
open Equality-with-substitutivity-and-contractibility′ (J⇒subst+contr eq) using (trans-sym)
import Equality.Tactic; open Equality.Tactic eq
import Equality.Misc; open Equality.Misc eq

private
  module Bijection where
    import Bijection; open Bijection eq public
open Bijection hiding (id; _∘_; inverse)

------------------------------------------------------------------------
-- A bijection between ((a₁ , b₁) ≡ (a₂ , b₂)) and
-- Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)

-- Compose equalities in a Σ type

Σ≡→≡Σ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
        Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) → (a₁ , b₁) ≡ (a₂ , b₂)
Σ≡→≡Σ B {a₁} {a₂} {b₁} {b₂} (a≡a , b≡b) = elim
  (λ {a₁ a₂} a≡a → ∀ {b₁ : B a₁} {b₂ : B a₂} → subst B a≡a b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂))
  (λ a → λ {b₁} {b₂} b≡b →
    (a , b₁)                  ≡⟨ cong (λ b → (a , b)) $ sym $ subst-refl B b₁ ⟩
    (a , subst B (refl a) b₁) ≡⟨ cong (λ b → (a , b)) b≡b ⟩∎
    (a , b₂)                  ∎)
  a≡a b≡b

private
  Σ≡→≡Σ-refl-refl′ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a : A} {b : B a} →
                      Σ≡→≡Σ B (refl a , subst-refl B b) ≡(
                      (a , b)                  ≡⟨ cong (λ b → (a , b)) $ sym $ subst-refl B b ⟩
                      (a , subst B (refl a) b) ≡⟨ cong (λ b → (a , b)) (subst-refl B b) ⟩∎
                      (a , b)                  ∎)
  Σ≡→≡Σ-refl-refl′ B {a} {b} = cong (λ fa → fa (subst-refl B b)) $ elim-refl
    (λ {a₁ a₂} a≡a → ∀ {b₁ : B a₁} {b₂ : B a₂} → subst B a≡a b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂))
    (λ a → λ {b₁} {b₂} b≡b →
      (a , b₁)                  ≡⟨ cong (λ b → (a , b)) $ sym $ subst-refl B b₁ ⟩
      (a , subst B (refl a) b₁) ≡⟨ cong (λ b → (a , b)) b≡b ⟩∎
      (a , b₂)                  ∎)
 
  Σ≡→≡Σ-refl-refl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a : A} {b : B a} →
                    Σ≡→≡Σ B (refl a , subst-refl B b) ≡ refl (a , b)
  Σ≡→≡Σ-refl-refl B {a} {b} =
    Σ≡→≡Σ B (refl a , subst-refl B b) ≡⟨ Σ≡→≡Σ-refl-refl′ B {a} {b} ⟩
    trans line1 line2                 ≡⟨ cong (λ p → trans p line2) $ cong-sym (λ b → (a , b)) $ subst-refl B b ⟩
    trans (sym line2) line2           ≡⟨ trans-symˡ line2 ⟩∎
    refl (a , b)∎
    where
      line1 : (a , b) ≡ (a , subst B (refl a) b)
      line1 = cong (λ b → (a , b)) $ sym $ subst-refl B b 
      line2 : (a , subst B (refl a) b) ≡ (a , b)
      line2 = cong (λ b → (a , b)) (subst-refl B b)

-- Decompose equalities for a Σ type

≡Σ→Σ≡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
        (a₁ , b₁) ≡ (a₂ , b₂) → Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)
≡Σ→Σ≡ {A = A} B {b₁ = b₁} {b₂ = b₂} s≡s = (a≡a , b≡b)
  where
    a≡a = cong proj₁ s≡s
    b≡b : subst B a≡a b₁ ≡ b₂
    b≡b =
      subst B a≡a b₁            ≡⟨ subst-cong B proj₁ s≡s b₁ ⟩
      subst (B ∘ proj₁) s≡s b₁  ≡⟨ cong[dep] (B ∘ proj₁) proj₂ s≡s ⟩∎
      b₂                        ∎

private
  ≡Σ→Σ≡-refl′ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a : A} {b : B a} →
                ≡Σ→Σ≡ B (refl (a , b)) ≡(
                  cong proj₁ (refl (a , b)) ,
                  (
                    subst B (cong proj₁ (refl (a , b))) b ≡⟨ subst-cong B proj₁ (refl (a , b) ) b ⟩
                    subst (B ∘ proj₁) (refl (a , b)) b    ≡⟨ cong[dep] (B ∘ proj₁) proj₂ (refl (a , b)) ⟩∎
                    b                                     ∎))
  ≡Σ→Σ≡-refl′ B = refl _

  ≡Σ→Σ≡-refl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a : A} {b : B a} →
                ≡Σ→Σ≡ B (refl (a , b)) ≡ (refl a , subst-refl B b)
  ≡Σ→Σ≡-refl B {a} {b} = 
                ≡Σ→Σ≡ B (refl (a , b))    ≡⟨ ≡Σ→Σ≡-refl′ B ⟩
                (a≡a , b≡b)               ≡⟨ Σ≡→≡Σ (λ p → subst B p b ≡ b) ( a≡a-path , lemma ) ⟩∎
                (refl a , subst-refl B b) ∎
    where
      a≡a = cong proj₁ (refl (a , b))
      a≡a-path = cong-refl proj₁

      b≡b-1 = subst-cong B proj₁ (refl (a , b) ) b
      b≡b-2 = cong[dep] (B ∘ proj₁) proj₂ (refl (a , b)) 
      b≡b = trans b≡b-1 b≡b-2
 
      lemma : subst (λ p → subst B p b ≡ b ) a≡a-path b≡b ≡ subst-refl B b
      lemma =
          subst (λ p → subst B p b ≡ b ) a≡a-path b≡b   ≡⟨ subst-path[simp] (λ p → subst B p b) (const b) a≡a-path b≡b ⟩
          trans path1 (trans b≡b path2)                 ≡⟨ cong (trans path1 ∘ trans b≡b) $ cong-const b a≡a-path ⟩
          trans path1 (trans b≡b (refl _))              ≡⟨ cong (trans path1) $ trans-reflʳ _ ⟩
          trans path1 b≡b                               ≡⟨ refl _ ⟩
          trans path1 (trans b≡b-1 b≡b-2)               ≡⟨ cong (λ p → trans path1 (trans p b≡b-2)) $ subst-cong-refl B proj₁ b ⟩
          trans path1 (trans b≡b-1′ b≡b-2)              ≡⟨ sym $ trans-assoc _ _ _ ⟩
          trans (trans path1 b≡b-1′) b≡b-2              ≡⟨ cong (λ p → trans p b≡b-2) $ trans-sym-trans _ _ ⟩
          trans (trans b≡b-1′-2 b≡b-1′-3) b≡b-2         ≡⟨ cong (trans $ trans b≡b-1′-2 b≡b-1′-3) $ cong[dep]-refl (B ∘ proj₁) proj₂ ⟩
          trans (trans b≡b-1′-2 b≡b-1′-3) b≡b-2′        ≡⟨ trans-trans-symʳ _ _ ⟩∎
          b≡b-1′-2                                      ∎
        where    
          b≡b-2′ = subst-refl (B ∘ proj₁) b

          b≡b-1′-1 = cong (λ p → subst B p b) a≡a-path
          b≡b-1′-2 = subst-refl B b
          b≡b-1′-3 = sym b≡b-2′

          b≡b-1′ = trans b≡b-1′-1 (trans b≡b-1′-2 b≡b-1′-3)

          path1 = sym b≡b-1′-1
          path2 = cong (const b) a≡a-path

private
  left-inverse-of : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
                 (p : (a₁ , b₁) ≡ (a₂ , b₂)) → Σ≡→≡Σ B (≡Σ→Σ≡ B p) ≡ p
  left-inverse-of B p =
    elim
      (λ {s₁ s₂} p → Σ≡→≡Σ B (≡Σ→Σ≡ B p) ≡ p)
      (λ s →
        Σ≡→≡Σ B (≡Σ→Σ≡ B (refl _))    ≡⟨ cong (Σ≡→≡Σ B) $ ≡Σ→Σ≡-refl B ⟩
        Σ≡→≡Σ B ( _ , _ )             ≡⟨ Σ≡→≡Σ-refl-refl B ⟩∎
        refl _                        ∎)
    p

  right-inverse-of-refl′ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a : A} →
                        {b₁ b₂ : B a} (p : b₁ ≡ b₂) →
                        ≡Σ→Σ≡ B (Σ≡→≡Σ B (refl a , (trans (subst-refl B b₁) p))) ≡ (refl a , (trans (subst-refl B b₁) p))
  right-inverse-of-refl′ B {a} =
    elim
      (λ {b₁ b₂} p → ≡Σ→Σ≡ B (Σ≡→≡Σ B (refl a , (trans (subst-refl B b₁) p))) ≡ (refl a , (trans (subst-refl B b₁) p)))
      (λ b →
        ≡Σ→Σ≡ B (Σ≡→≡Σ B (refl a , (trans (subst-refl B b) (refl _))))    ≡⟨ cong (≡Σ→Σ≡ B ∘ Σ≡→≡Σ B ∘ _,_ (refl a)) $ trans-reflʳ _ ⟩
        ≡Σ→Σ≡ B (Σ≡→≡Σ B (refl a , subst-refl B b))                       ≡⟨ cong (≡Σ→Σ≡ B) $ Σ≡→≡Σ-refl-refl B ⟩
        ≡Σ→Σ≡ B (refl _ )                                                 ≡⟨ ≡Σ→Σ≡-refl B ⟩
        (refl a , subst-refl B b )                                        ≡⟨ cong (λ p → (refl a , p)) $ sym $ trans-reflʳ _ ⟩∎
        (refl a , (trans (subst-refl B b) (refl _)))                      ∎)

  right-inverse-of-refl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a : A} →
                        {b₁ b₂ : B a} (p : subst B (refl a) b₁ ≡ b₂) →
                        ≡Σ→Σ≡ B (Σ≡→≡Σ B (refl a , p)) ≡ (refl a , p)
  right-inverse-of-refl B {a} {b₁} {b₂} p =
      ≡Σ→Σ≡ B (Σ≡→≡Σ B (refl a , p))                                      ≡⟨ cong (≡Σ→Σ≡ B ∘ Σ≡→≡Σ B ∘ _,_ (refl a)) $ sym $ trans-transʳ-sym _ _ ⟩
      ≡Σ→Σ≡ B (Σ≡→≡Σ B (refl a , (trans shift (trans (sym shift) p))))    ≡⟨ right-inverse-of-refl′ B _ ⟩
      (refl a , trans shift (trans (sym shift) p))                        ≡⟨ cong (_,_ (refl a)) $ trans-transʳ-sym _ _ ⟩∎
      (refl a , p)                                                        ∎
    where
      shift : subst B (refl a) b₁ ≡ b₁
      shift = subst-refl B b₁

  right-inverse-of : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
                  (s : Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)) → ≡Σ→Σ≡ B (Σ≡→≡Σ B s) ≡ s
  right-inverse-of B (pa , pb) =
    elim
      (λ {a₁ a₂} pa → {b₁ : B a₁} {b₂ : B a₂} (pb : subst B pa b₁ ≡ b₂) → ≡Σ→Σ≡ B (Σ≡→≡Σ B (pa , pb)) ≡ (pa , pb))
      (λ a pb → right-inverse-of-refl B pb)
      pa pb

------------------------------------------------------------------------
-- Composition and decomposition form a bijection!

≡Σ↔Σ≡ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} →
          ((a₁ , b₁) ≡ (a₂ , b₂)) ↔ Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)
≡Σ↔Σ≡ B {a₁} {a₂} {b₁} {b₂} =
  record
  { surjection = record
    { equivalence = record
      { to = ≡Σ→Σ≡ B
      ; from = Σ≡→≡Σ B
      }
    ; right-inverse-of = right-inverse-of B
    }
  ; left-inverse-of = left-inverse-of B
  }
