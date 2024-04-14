module Lib.Zero where

data 𝟘 : Set where

zero-elim : {A : Set} → 𝟘 → A
zero-elim ()

Not : Set → Set
Not A = A → 𝟘

¬_ : Set → Set
¬_ = Not
