module Lib.Nat where

open import Lib.Zero using (𝟘)
open import Lib.One using (𝟙)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ -> ℕ -> ℕ
zero  + m = m
suc n + m = suc (n + m)

{-# BUILTIN NATPLUS _+_ #-}

_≤_ : ℕ → ℕ → Set
zero  ≤ m     = 𝟙
suc n ≤ zero  = 𝟘
suc n ≤ suc m = n ≤ m

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m
