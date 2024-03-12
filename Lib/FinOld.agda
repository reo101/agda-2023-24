module Lib.FinOld where

open import Level using (zero; suc)

open import Lib.Nat using (ℕ; zero; suc; _+_; _<_)
open import Lib.Utils using (id; const; constⁱ)
open import Lib.One using (𝟙)
open import Lib.Two renaming (𝟚 to Bool; tt to true; ff to false)
open import Lib.Equality using (_≡_; refl)
open import Lib.Number using (Number; fromNat)

-- data Fin : ℕ → Set where
--   zero : {n : ℕ} → Fin (suc n)
--   suc : {n : ℕ} → Fin n → Fin (suc n)
--
-- data IsTrue : Bool → Set where
--   itis : IsTrue true
--
-- instance
--   indeed : IsTrue true
--   indeed = itis
--
-- _<?_ : ℕ → ℕ → Bool
-- zero  <? zero  = false
-- zero  <? suc y = true
-- suc x <? zero  = false
-- suc x <? suc y = x <? y
--
-- natToFin : ∀ {n} (m : ℕ) {{_ : IsTrue (m <? n)}} → Fin n
-- natToFin {zero}  zero    {{()}}
-- natToFin {zero}  (suc m) {{()}}
-- natToFin {suc n} zero    {{itis}} = zero
-- natToFin {suc n} (suc m) {{t}}    = suc (natToFin m)
--
-- instance
--   NumFin : ∀ {n} → Number (Fin n)
--   Number.Constraint (NumFin {n}) k = IsTrue (k <? n)
--   Number.fromNat    NumFin       k = natToFin k
--
-- instance
--   Numℕ : ∀ {_} → Number ℕ
--   Number.Constraint (Numℕ {n}) = const (IsTrue true)
--   Number.fromNat    Numℕ     k = k
--
-- _ : Fin 6
-- _ = 3
