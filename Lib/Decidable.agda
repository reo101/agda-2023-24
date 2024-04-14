module Lib.Decidable where

open import Lib.Zero using (𝟘; ¬_)

data Dec (A : Set) : Set where
  no  : ¬ A -> Dec A
  yes : A -> Dec A
