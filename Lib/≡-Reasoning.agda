open import Level using (Level; _⊔_; suc)

module Lib.≡-Reasoning where

open import Lib.Equality using (_≡_; refl)

private
  variable
    n m   : Level
    A     : Set n
    B     : Set m
    x y z : A

module Helpers where

  trans : x ≡ y →
          y ≡ z →
          -------
          x ≡ z
  trans refl refl = refl

  sym : x ≡ y →
        -------
        y ≡ x
  sym refl = refl

  cong : (f : A → B) →
         -------------
         x ≡ y →
         -------
         f x ≡ f y
  cong f refl = refl

  cong-app : {f g : A → B} →
             ---------------
             f ≡ g →
             -------
             ∀ (x : A) → f x ≡ g x
  cong-app refl x = refl

  subst : (P : A → Set) →
          ---------------
          x ≡ y →
          P x →
          -------
          P y
  subst P refl px = px

open Helpers public

infix  1 begin_
infixr 2 _≡⟨⟩_ step-≡
infix  3 _∎

begin_ : ∀ {x y : A} →
         -------------
         x ≡ y →
         -----
         x ≡ y
begin x≡y = x≡y

_≡⟨⟩_ : ∀ (x : A)
        {y : A} →
        ---------
        x ≡ y →
        -----
        x ≡ y
x ≡⟨⟩ x≡y = x≡y

step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ x y≡z x≡y = trans x≡y y≡z

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

_∎ : ∀ (x : A) →
    ------------
    x ≡ x
x ∎ = refl
