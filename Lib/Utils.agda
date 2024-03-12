module Lib.Utils where

open import Level using (Level)

private
  variable
    n m l : Level
    A : Set n
    B : Set m
    C : Set l

const : A → B → A
const x _ = x

constⁱ : A → {B} → A
constⁱ x {_} = x

id : A → A
id x = x

flip : (A → B → C) → B → A → C
flip f y x = f x y

_∘_ : (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)
