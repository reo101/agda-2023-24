module Lib.Vec where

open import Lib.Nat using (ℕ; zero; suc; _+_)

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (1 + n)

infixr 20 _∷_

map : ∀ {A B} → ∀ {n} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs
