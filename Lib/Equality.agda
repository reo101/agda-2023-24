module Lib.Equality where

open import Agda.Primitive using (Level; lzero; lsuc)

-- data _≡_ {A : Set} : A → A → Set where
--   refl : {x : A} → x ≡ x

data _≡_ {n : Level} {A : Set n} : A → A → Set n where
  refl : {x : A} → x ≡ x

infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

---------------
--- HELPERS ---
---------------

private
  variable
    n m : Level
    A   : Set n
    B   : Set m
    x y : A

cong : (f : A → B) →
       -----------
       x ≡ y →
       -------
       f x ≡ f y
cong f refl = refl

cong-app : {f g : A → B} →
           ---------------
           f ≡ g →
           -------
           ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : (P : A → Set) →
        ---------------
        x ≡ y →
        P x →
        -------
        P y
subst P refl px = px
