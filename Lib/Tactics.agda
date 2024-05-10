module Lib.Tactics where

open import Agda.Builtin.Unit using (⊤)
open import Reflection using (Term; TC; bindTC; quoteTC; unify)

default : {A : Set} → A → Term → TC ⊤
default x hole = bindTC (quoteTC x) (unify hole)
