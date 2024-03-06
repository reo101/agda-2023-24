module Lib.Two where

data 𝟚 : Set where
  tt : 𝟚
  ff : 𝟚

{-# BUILTIN BOOL  𝟚  #-}
{-# BUILTIN TRUE  tt #-}
{-# BUILTIN FALSE ff #-}

not : 𝟚 → 𝟚
not tt = ff
not ff = tt

_∧_ : 𝟚 → 𝟚 → 𝟚
tt ∧ y = y
ff ∧ _ = ff

infixr 15 _∧_

_∨_ : 𝟚 → 𝟚 → 𝟚
ff ∨ y = y
tt ∨ _ = tt

infixr 15 _∨_
