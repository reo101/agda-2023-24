module Lib.Number where

open import Level using (suc)

open import Lib.Nat using (ℕ; _<_)
open import Lib.One using (𝟙)
open import Lib.Fin using (Fin; natToFin)

record Number {a} (A : Set a) : Set (suc a) where
  field
    Constraint : ℕ → Set a
    fromNat : (n : ℕ) {{_ : Constraint n}} → A

open Number {{...}} public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}
{-# DISPLAY Number.fromNat _ n = fromNat n #-}

-----------------
--- INSTANCES ---
-----------------

instance
  Numℕ : Number ℕ
  Number.Constraint Numℕ _ = 𝟙
  Number.fromNat    Numℕ k = k

_ : ℕ
_ = 3

instance
  NumFin : ∀ {n} → Number (Fin n)
  Number.Constraint (NumFin {n}) k         = k < n
  Number.fromNat    (NumFin {n}) k {{k<n}} = natToFin k {k<n}

_ : Fin 6
_ = 4

_ : {A : Set} → Fin 0 → A
_ = λ ()
