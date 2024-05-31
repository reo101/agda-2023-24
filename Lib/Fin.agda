module Lib.Fin where

open import Lib.Nat using (ℕ; zero; suc; _<_)
open import Lib.One using (𝟙; ⟨⟩)

-- record Fin (n : ℕ) : Set where
--   constructor _[_]
--   field
--     ⟦_⟧ : ℕ
--     proof : ⟦_⟧ < n

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

natToFin : ({n} m : ℕ) → {m < n} → Fin n
natToFin {zero}  zero    {()}
natToFin {zero}  (suc m) {()}
natToFin {suc n} zero    {⟨⟩} = zero
natToFin {suc n} (suc m) {pr} = suc (natToFin m {pr})

finToNat : {n : ℕ} → Fin n → ℕ
finToNat zero = zero
finToNat (suc n) = suc (finToNat n)
