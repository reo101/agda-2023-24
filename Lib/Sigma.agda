module Lib.Sigma where

record ∃ (A : Set) (P : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : P fst
open ∃ public

infixr 15 _,_

infixr 8 ∃ Σ

Σ : (A : Set) (P : A → Set) → Set
Σ = ∃

_*_ : Set -> Set -> Set
A * B = ∃ A \_ -> B

infixr 9 _*_
