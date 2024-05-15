module Joro.FiveLive where

open import Lib.Zero using (𝟘)
open import Lib.One using (𝟙)
open import Lib.Two using (𝟚)
open import Lib.Nat using (ℕ; zero; suc; ozero; osuc; _+_; _≤_; +-right-suc)
open import Lib.Sigma using (Σ; _,_)
open import Lib.Decidable using (Dec; no; yes)
open import Lib.List using (List; []; _,-_; length)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

data Even : ℕ → Set where
  e-zero : Even 0
  e-sucsuc : {n : ℕ} → Even n → Even (suc (suc n))

-- (1 + m) - (1 + n)
-- m - n
diff :
  (m : ℕ) (n : ℕ) →
  n ≤ m →
  Σ ℕ \d → n + d ≡ m
diff m zero p = m , refl
diff zero (suc n) ()
diff (suc m) (suc n) (osuc p) with diff m n p
... | d' , q = d' , cong suc q

decℕ≡ : (n m : ℕ) → Dec (n ≡ m)
decℕ≡ zero zero = yes refl
decℕ≡ zero (suc m) = no \ ()
decℕ≡ (suc n) zero = no \ ()
decℕ≡ (suc n) (suc m) with decℕ≡ n m
... | no p = no \ { refl → p refl }
... | yes refl = yes refl

+-assoc' : (n m k : ℕ) → (n + m) + k ≡ n + (m + k)
+-assoc' zero m k = refl
+-assoc' (suc n) m k with (n + m) + k | +-assoc' n m k
... | .(n + m + k) | refl = refl

-- ————————————————————————————————————————————————————————————
-- Goal: suc ((n + m) + k) ≡ suc n + m + k
-- ————————————————————————————————————————————————————————————
-- k m n : ℕ
-- ————————————————————————————————————————————————————————————

-- show sigma
-- sigma as "exists"
-- sigma for unknown input
-- show Dec
-- show with
--   diff
--     full syntax
--     dots
--     we can still rewrite
--   decℕ≡
--     matching on the with value gives us more info
--   rewrite with with, +-assoc, abstracting types over values
--     goal+original args types' are abstracted over the with value
-- show Fin
-- show Vec

data Vec (A : Set) : ℕ → Set where
  [] : Vec A 0
  _,-_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 20 _,-_

_ : List ℕ
_ = 3 ,- 4 ,- 5 ,- []

_ : Vec ℕ 3
_ = 3 ,- 4 ,- 5 ,- []

-- n ~ 0
-- n ~ suc n'
vHead : {A : Set} {n : ℕ} → Vec A (suc n) → A
vHead (x ,- xs) = x

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

-- x = suc (suc zero) : Fin 3
-- suc x : Fin 4

_ : Fin 3
_ = zero

_ : Fin 3
_ = suc zero

_ : Fin 3
_ = suc (suc zero)





-- TASK
-- Use Σ to specify, and then implement division by two,
-- which guarantees that the result is twice as small as the input.
--
-- Note that we don't need an explicit n since Even already has enough
-- info to let Agda figure out what n should be
div2 : {n : ℕ} → Even n → Σ ℕ λ m → m + m ≡ n
div2 e-zero = zero , refl
div2 {n = suc (suc n-2)} (e-sucsuc n-2even) with (div2 n-2even)
... | m-1 , m-1+m-1≡n-2 =
      suc m-1 ,
      (begin
          suc m-1 + suc m-1
        ∼⟨⟩
          suc (m-1 + suc m-1)
        ∼⟨ cong suc (symmetric (+-right-suc m-1 m-1)) ⟩
          suc (suc (m-1 + m-1))
        ∼⟨ cong suc (cong suc m-1+m-1≡n-2) ⟩
          suc (suc n-2)
      ∎)

-- TASK
-- Express List by using Vec and Σ
ListAsVec : Set → Set
ListAsVec A = Σ ℕ (Vec A)

-- TASK
-- Convert from ListAsVec to List
ListAsVec-to-List : {A : Set} → ListAsVec A → List A
ListAsVec-to-List (zero , []) = []
ListAsVec-to-List (suc len , x ,- xs) = x ,- ListAsVec-to-List (len , xs)

-- TASK
-- Convert from List to ListAsVec
List-to-ListAsVec : {A : Set} → List A → ListAsVec A
List-to-ListAsVec [] = zero , []
List-to-ListAsVec (x ,- xs) with List-to-ListAsVec xs
... | len , xsv = suc len , x ,- xsv

-- TASK
-- Formulate and prove that the ListAsVec conversions do not change their respective inputs

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Isomorphism using (Isomorphism)
open import Project.Postulates using (funext)

takovata : {A : Set} → Isomorphism HASK (ListAsVec-to-List {A}) (List-to-ListAsVec {A})
Isomorphism.isomorphismˡ takovata = funext λ
  { (zero , []) → refl
  ; (suc len , x ,- xs) → {!!}
    -- begin
    --   ?
    -- ∼⟨ ? ⟩
    --   ?
    -- ∎
  }
Isomorphism.isomorphismʳ takovata = funext λ
  { [] → refl
  ; (x ,- xs) →
    begin
      ?
    ∼⟨ ? ⟩
      ?
    ∎
  }

-- TASK
-- Formulate and implement "precise", List → Vec conversion
-- in the sense that you can exactly specify what the length of the resulting vector will be
listToVec : {A : Set} (xs : List A) → Vec A (length xs)
listToVec [] = []
listToVec (x ,- xs) = x ,- listToVec xs

-- TASK
-- Specify and implement vector appending
_+V_ : {A : Set} {n m : ℕ} (xs : Vec A n) (ys : Vec A m) → Vec A (n + m)
[] +V ys = ys
(x ,- xs) +V ys = x ,- xs +V ys
infixr 25 _+V_

{-
-- TASK
-- Specify and implement the map function for vectors
vMap : ?
vMap = {! !}

-- TASK
-- Specify and implement the cartesian product of two vectors
_*V_ : ?
_*V_ = {! !}

-- TASK
-- Use an input value of type n ≤ m to guide you on how to take a prefix of size n from an input Vector of size m.
vTake : ?
vTake = ?

-- TASK
-- Look at ≤-refl.
-- Think about what property you can prove involving vTake and ≤-refl.

-- TASK
-- Look at ≤-trans
-- Formulate and prove the following property:
--
-- If you know n ≤ m and m ≤ k, and you have Vec A k,
-- then both of these operations should have the same result:
-- * doing two vTakes - one with n ≤ m, and another with m ≤ k,
-- * doing a single vTake - with the "composition" of n ≤ m and m ≤ k

-- TASK
-- Convert a Fin to a ℕ
-- Essentially this "forgets" the upper bound for the input Fin
finToℕ : {n : ℕ} → Fin n → ℕ
finToℕ = {!!}

-- TASK
-- express < by using _≤_ without using _≡_
_<_ : ℕ → ℕ → Set
n < m = {!!}

infix 90 _<_

-- TASK
<-suc : (n : ℕ) → n < suc n
<-suc = {!!}

-- TASK
-- Convert a ℕ to a Fin
natToFin : ?
natToFin = ?

-- TASK
-- A generalised version of natToFin, which uses < to specify what the upper
-- bound for the resulting Fin is
natToFin< : {m : ℕ} (n : ℕ) → n < m → Fin m
natToFin< = ?

-- TASK
finToℕ-natToFin-id : (n : ℕ) → n ≡ finToℕ (natToFin n)
finToℕ-natToFin-id = {!!}

-- TASK
-- Write down the calculated version of <, i.e. instead of defining a data type
-- implement the function Lt which takes two ℕs and returns what proof is required
-- to prove they are equal.
-- You can look at TwoEq in Lecture/TwoStart.agda for inspiration.
Lt : ℕ → ℕ → Set
Lt = {!!}

-- TASK
-- Prove that the calculated version of _<_ implies the regular on
Lt-< : (n m : ℕ) → Lt n m → n < m
Lt-< = {!!}

-- TASK
-- "Weaken" the upper bound for a Fin.
-- "Weaken", because we allow *more* values in the new Fin,
-- meaning we have *less* information about what the result actually is.
weakenFin : {m n : ℕ} → Fin n → n ≤ m → Fin m
weakenFin = {!!}

-- TASK
-- Specialised version of weakenFin, might be useful some other day
-- look at ≤-suc in Lib.ℕ
weakenFinSuc : {n : ℕ} → Fin n → Fin (suc n)
weakenFinSuc = {!!}

-- TASK
-- Prove that _<_ implies _≤_
<-≤ : {n m : ℕ} → n < m → n ≤ m
<-≤ = {!!}

-- TASK
finToℕ-< : {n : ℕ} → (x : Fin n) → finToℕ x < n
finToℕ-< = {!!}

-- TASK
fromℕ-toℕ-id : {m n : ℕ} (x : Fin n) (p : n ≤ m) → x ≡ natToFin (finToℕ x) (finToℕ-< x)
fromℕ-toℕ-id = {!!}

-- TASK
-- Implement an equality check for Fins
decEqFin : {n : ℕ} → (x y : Fin n) → Dec (x ≡ y)
decEqFin = {!!}
-}
