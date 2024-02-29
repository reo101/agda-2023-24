module Lib.Equality where

open import Agda.Primitive using (lzero; lsuc)

-- data _≡_ {A : Set} : A → A → Set where
--   refl : {x : A} → x ≡ x

data _≡_ {n} {A : Set n} : A → A → Set n where
  refl : {x : A} → x ≡ x

infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
