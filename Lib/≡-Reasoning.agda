open import Level using (Level; _⊔_; suc)

open import Lib.Equality using (_≡_; refl)

module Lib.≡-Reasoning {n : Level} {A : Set n} where

infix  1 begin_
infixr 2 _≡⟨⟩_ step-≡
infix  3 _∎

trans : ∀ {n} → ∀ {A : Set n} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

sym : ∀ {n} → ∀ {A : Set n} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

cong : ∀ {n m} → ∀ {A : Set n} {B : Set m} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl  =  refl

cong-app : ∀ {n m} → ∀ {A : Set n} {B : Set m} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

begin_ : ∀ {x y : A}
  → x ≡ y
    -----
  → x ≡ y
begin x≡y = x≡y

_≡⟨⟩_ : ∀ (x : A) {y : A}
  → x ≡ y
    -----
  → x ≡ y
x ≡⟨⟩ x≡y = x≡y

step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ x y≡z x≡y = trans x≡y y≡z

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

_∎ : ∀ (x : A)
    -----
  → x ≡ x
x ∎ = refl
