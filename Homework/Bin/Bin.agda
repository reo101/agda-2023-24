module Homework.Bin.Bin where

open import Lib.Nat using (ℕ) renaming (_+_ to _+N_; _*_ to _*N_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

open import Project.Postulates using (funext)

open import Project.Data.Pair using (Pair; _,_)

open import Lib.Zero using (𝟘)
open import Lib.One using (𝟙)
open import Lib.Two using (𝟚; tt; ff; not; if_then_else_)

data Bin : Set where
  ✂  : Bin
  _𝟎 : Bin -> Bin
  _𝟏 : Bin -> Bin

infixr 12 _𝟎
infixr 12 _𝟏

_ : Bin
_ = ✂ 𝟏 𝟎 𝟏

suc : Bin -> Bin
suc ✂ = ✂ 𝟏
suc (b 𝟎) = b 𝟏
suc (b 𝟏) = suc b 𝟎

_ : suc ✂ ≡ ✂ 𝟏
_ = refl

_ : suc (✂ 𝟏 𝟏) ≡ ✂ 𝟏 𝟎 𝟎
_ = refl

-- (n / 2 , n % 2)
natDivTwo : ℕ → Pair ℕ 𝟚
natDivTwo ℕ.zero = ℕ.zero , ff
natDivTwo (ℕ.suc n) with natDivTwo n
...                   | m , tt = ℕ.suc m , ff
...                   | m , ff = m , tt

toNat : Bin -> ℕ
toNat ✂ = ℕ.zero
toNat (b 𝟎) = 2 *N toNat b
toNat (b 𝟏) = 1 +N 2 *N toNat b

_ : toNat (✂ 𝟏 𝟏 𝟏) ≡ 7
_ = refl

_ : toNat (✂ 𝟏 𝟏 𝟎) ≡ 6
_ = refl

_ : toNat (✂ 𝟎) ≡ 0
_ = refl

_ : toNat ✂ ≡ 0
_ = refl

fromNat : ℕ -> Bin
fromNat ℕ.zero = ✂
fromNat (ℕ.suc x) = suc (fromNat x)

_ : fromNat 0 ≡ ✂
_ = refl

_ : fromNat 1 ≡ ✂ 𝟏
_ = refl

_ : fromNat 8 ≡ ✂ 𝟏 𝟎 𝟎 𝟎
_ = refl

toNat-suc : (b : Bin) -> toNat (suc b) ≡ ℕ.suc (toNat b)
toNat-suc ✂ = refl
toNat-suc (b 𝟎) = refl
toNat-suc (b 𝟏) =
  begin
    toNat (suc (b 𝟏))
  ∼⟨⟩
    toNat (suc b) +N (toNat (suc b) +N ℕ.zero)
  ∼⟨ cong (toNat (suc b) +N_) (lemma1 (toNat (suc b))) ⟩
    toNat (suc b) +N toNat (suc b)
  ∼⟨ cong-app (cong _+N_ (toNat-suc b)) (toNat (suc b)) ⟩
    ℕ.suc (toNat b) +N toNat (suc b)
  ∼⟨ cong (ℕ.suc (toNat b) +N_) (toNat-suc b) ⟩
    ℕ.suc (toNat b) +N ℕ.suc (toNat b)
  ∼⟨⟩
    ℕ.suc (toNat b +N ℕ.suc (toNat b))
  ∼⟨ cong ℕ.suc (lemma2 (toNat b) (toNat b)) ⟩
    ℕ.suc (ℕ.suc (toNat b +N toNat b))
  ∼⟨ cong ℕ.suc (cong ℕ.suc (cong (toNat b +N_) (symmetric (lemma1 (toNat b))))) ⟩
    ℕ.suc (ℕ.suc (toNat b +N (toNat b +N ℕ.zero)))
  ∼⟨⟩
    ℕ.suc (toNat (b 𝟏))
  ∎
  where
    lemma1 : (n : ℕ) → n +N ℕ.zero ≡ n
    lemma1 ℕ.zero = refl
    lemma1 (ℕ.suc n) =
      begin
        ℕ.suc n +N ℕ.zero
      ∼⟨⟩
        ℕ.suc (n +N ℕ.zero)
      ∼⟨ cong ℕ.suc (lemma1 n) ⟩
        ℕ.suc n
      ∎

    lemma2 : (n m : ℕ) → n +N ℕ.suc m ≡ ℕ.suc (n +N m)
    lemma2 ℕ.zero m = refl
    lemma2 (ℕ.suc n) m =
      begin
        ℕ.suc n +N ℕ.suc m
      ∼⟨⟩
        ℕ.suc (n +N ℕ.suc m)
      ∼⟨ cong ℕ.suc (lemma2 n m) ⟩
        ℕ.suc (ℕ.suc n +N m)
      ∎

to-from-id : (n : ℕ) -> toNat (fromNat n) ≡ n
to-from-id ℕ.zero = refl
to-from-id (ℕ.suc n) =
  begin
    toNat (fromNat (ℕ.suc n))
  ∼⟨⟩
    toNat (suc (fromNat n))
  ∼⟨ toNat-suc (fromNat n) ⟩
    ℕ.suc (toNat (fromNat n))
  ∼⟨ cong ℕ.suc (to-from-id n) ⟩
    ℕ.suc n
  ∎

data LeadingOne : Bin -> Set where
  ✂𝟏 : LeadingOne (✂ 𝟏)
  _𝟎 : {b : Bin} -> LeadingOne b -> LeadingOne (b 𝟎)
  _𝟏 : {b : Bin} -> LeadingOne b -> LeadingOne (b 𝟏)

data Can : Bin -> Set where
  ✂ : Can ✂
  leadingOne : {b : Bin} -> LeadingOne b -> Can b

suc-LeadingOne : (b : Bin) -> LeadingOne b -> LeadingOne (suc b)
suc-LeadingOne = {! !}

suc-Can : (b : Bin) -> Can b -> Can (suc b)
suc-Can = {! !}

fromNat-Can : (n : ℕ) -> Can (fromNat n)
fromNat-Can = {! !}

_+B_ : Bin -> Bin -> Bin
_+B_ = {! !}

infixr 11 _+B_

_ : ✂ +B ✂ 𝟏 𝟏 𝟏 𝟏 ≡ ✂ 𝟏 𝟏 𝟏 𝟏
_ = refl

_ : ✂ 𝟏 𝟎 𝟎 +B ✂ ≡ ✂ 𝟏 𝟎 𝟎
_ = refl

_ : ✂ 𝟏 𝟏 +B ✂ 𝟏 𝟏 𝟏 𝟏 ≡ ✂ 𝟏 𝟎 𝟎 𝟏 𝟎
_ = refl

_ : ✂ 𝟏 𝟏 𝟏 +B ✂ 𝟏 𝟎 𝟏 ≡ ✂ 𝟏 𝟏 𝟎 𝟎
_ = refl

+B-right-end : (b : Bin) -> b +B ✂ ≡ b
+B-right-end = {! !}

+B-left-suc : (b v : Bin) -> suc b +B v ≡ suc (b +B v)
+B-left-suc = {! !}

+B-right-suc : (b v : Bin) -> b +B suc v ≡ suc (b +B v)
+B-right-suc = {! !}

fromNat-+N-+B-commutes : (n m : ℕ) -> fromNat (n +N m) ≡ fromNat n +B fromNat m
fromNat-+N-+B-commutes = {! !}

+B-same-shift : (b : Bin) -> LeadingOne b -> b +B b ≡ b 𝟎
+B-same-shift = {! !}

from-to-id-Can : (b : Bin) -> Can b -> fromNat (toNat b) ≡ b
from-to-id-Can = {! !}
