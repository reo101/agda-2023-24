module Lib.Nat where

open import Lib.Zero using (𝟘; ¬_)
open import Lib.One using (𝟙)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
infixr 100 _+_

{-# BUILTIN NATPLUS _+_ #-}

_<=_ : ℕ → ℕ → Set
zero  <= m     = 𝟙
suc n <= zero  = 𝟘
suc n <= suc m = n <= m

_<_ : ℕ → ℕ → Set
n < m = suc n <= m

-- _*_  : ℕ → ℕ → ℕ
-- zero * y = zero
-- suc x * y = y + (x * y)
-- infixr 120 _*_

---

+-assoc : (n m k : ℕ) → (n + m) + k ≡ n + (m + k)
+-assoc zero m k = refl
+-assoc (suc n) m k = cong suc (+-assoc n m k)

+-right-zero : (n : ℕ) → n + zero ≡ n
+-right-zero zero = refl
+-right-zero (suc n) =
  cong suc (+-right-zero n)

+-right-suc : (n m : ℕ) → suc (n + m) ≡ n + suc m
+-right-suc zero m = refl
+-right-suc (suc x) m = cong suc (+-right-suc x m)

+-commut : (n m : ℕ) → n + m ≡ m + n
+-commut zero m = symmetric (+-right-zero m)
+-commut (suc n) m
  rewrite +-commut n m
  rewrite +-right-suc m n =
  refl

data _≤_ : ℕ → ℕ → Set where
  -- We know that zero is ≤ anything else
  ozero : {x : ℕ} → zero ≤ x
  -- We know that if x ≤ y, then suc x ≤ suc y also
  osuc : {x y : ℕ} → x ≤ y → suc x ≤ suc y

infix 90 _≤_

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = ozero
≤-refl (suc x) = osuc (≤-refl x)

≤-suc : (n : ℕ) → n ≤ suc n
≤-suc zero = ozero
≤-suc (suc x) = osuc (≤-suc x)

≤-trans : {n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
≤-trans ozero q = ozero
≤-trans (osuc p) (osuc q) = osuc (≤-trans p q)

≤-antisymm : {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
≤-antisymm ozero ozero = refl
≤-antisymm (osuc p) (osuc q) = cong suc (≤-antisymm p q)

≤-refl-not-suc : {n : ℕ} → ¬ (suc n ≤ n)
≤-refl-not-suc (osuc sucn≤m) = ≤-refl-not-suc sucn≤m

≤-suc-not-eq : {n m : ℕ} → suc n ≤ m → ¬ (n ≡ m)
≤-suc-not-eq p refl = ≤-refl-not-suc p

ℕEq : ℕ → ℕ → Set
ℕEq zero zero = 𝟙
ℕEq zero (suc m) = 𝟘
ℕEq (suc n) zero = 𝟘
ℕEq (suc n) (suc m) = ℕEq n m

_*_  : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + n * m
infixr 120 _*_

*-right-zero : (n : ℕ) → n * 0 ≡ 0
*-right-zero zero = refl
*-right-zero (suc n) = *-right-zero n

*-right-suc : (n m : ℕ) → n * suc m ≡ n + n * m
*-right-suc zero m = refl
*-right-suc (suc n) m rewrite *-right-suc n m = cong suc (
  begin
  m + n + n * m ∼⟨ symmetric (+-assoc m n (n * m)) ⟩
  (m + n) + n * m ∼⟨ cong (_+ n * m) (+-commut m n) ⟩
  (n + m) + n * m ∼⟨ +-assoc n m (n * m) ⟩
  n + m + n * m
  ∎)

*-commut : (n m : ℕ) → n * m ≡ m * n
*-commut zero m rewrite *-right-zero m = refl
*-commut (suc n) m =
  begin
    m + n * m
  ∼⟨ cong (m +_) (*-commut n m) ⟩
    m + m * n
  ∼⟨ symmetric (*-right-suc m n) ⟩
    m * suc n
  ∎

*-left-distrib-+ : (n m k : ℕ) → n * (m + k) ≡ n * m + n * k
*-left-distrib-+ zero m k = refl
*-left-distrib-+ (suc n) m k =
  begin
    (m + k) + n * (m + k)
  ∼⟨ cong ((m + k) +_) (*-left-distrib-+ n m k) ⟩
    (m + k) + (n * m + n * k)
  ∼⟨ +-assoc m k (n * m + n * k) ⟩
    m + (k + ((n * m) + (n * k)))
  ∼⟨ cong (m +_) (symmetric (+-assoc k (n * m) (n * k))) ⟩
    m + ((k + (n * m)) + (n * k))
  ∼⟨ cong (m +_) (cong-app (cong _+_ (+-commut k (n * m))) _) ⟩
    m + (((n * m) + k) + (n * k))
  ∼⟨ cong (m +_) (+-assoc (n * m) k (n * k)) ⟩
    m + ((n * m) + (k + (n * k)))
  ∼⟨ symmetric (+-assoc m (n * m) (k + n * k)) ⟩
    (m + n * m) + (k + n * k)
  ∎

*-right-distrib-+ : (n m k : ℕ) → (n + m) * k ≡ n * k + m * k
*-right-distrib-+ n m k
  rewrite *-commut (n + m) k
  rewrite *-left-distrib-+ k n m
  rewrite *-commut k n
  rewrite *-commut k m = refl

*-assoc : (n m k : ℕ) → (n * m) * k ≡ n * (m * k)
*-assoc zero m k = refl
*-assoc (suc n) m k =
  begin
    (suc n * m) * k
  ∼⟨⟩
    (m + n * m) * k
  ∼⟨ *-right-distrib-+ m (n * m) k ⟩
    m * k + (n * m) * k
  ∼⟨ cong (m * k +_) (*-assoc n m k) ⟩
    suc n * m * k
  ∎
