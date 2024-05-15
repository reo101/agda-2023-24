module Joro.EightLive where

open import Lib.Zero using (𝟘; zero-elim)
open import Lib.One using (𝟙; ⟨⟩)
open import Lib.Two using (𝟚; tt; ff)
open import Lib.Nat using (ℕ; zero; suc; ozero; osuc; _≤_; ≤-suc; ≤-trans; +-right-suc) renaming (_<_ to Lt)
open import Lib.Fin using (Fin; zero; suc; natToFin)
open import Lib.Number using (Number; fromNat; Numℕ; NumFin)
open import Lib.Sum using (_+_; inl; inr)
open import Lib.Sigma using (Σ; _,_; fst; snd; _*_)
open import Lib.Decidable using (Dec; no; yes)
open import Lib.List using (List; []; _∷_; length)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

_ : Fin 6
_ = 4

-- data Fin : ℕ → Set where
--   zero : {n : ℕ} → Fin (suc n)
--   suc : {n : ℕ} → Fin n → Fin (suc n)

-- weakenFinSuc : {n : ℕ} → Fin n → Fin (suc n)
-- weakenFinSuc (3 :: горна граница 4) ≡ (3 :: горна граница 5)

-- LECTURE:
-- https://learn.fmi.uni-sofia.bg/mod/url/view.php?id=312944

-- Fin 3
-- 0 1 2
-- zero
-- suc zero
-- suc (suc zero)
-- "тип с три обитателя"
-- Λₙ := "има по-малко от (1 + n) свободни променливи"
-- Fin n
--
-- Fin n
-- "тип с n обитателя"

-- tl;dr we need some Fin and < machinery later down the line for lambda terms.
--
-- The tasks below concerning Fins and comparisons are necessary,
-- because when we're expressing nameless lambda terms, we'll want to be able to say
-- "at most n free variables", which is exactly the same as "the number of free variables being less than n".
-- At the same time, a term of Fin n is exactly the same as a number which is less than n,
-- which we'll use for constructing variables.

-- TASK
-- "Forget" the type information of the upper bound of a Fin, only leaving the number itself.
toℕ : {n : ℕ} → Fin n → ℕ
toℕ Fin.zero = 0
toℕ (Fin.suc f) = suc (toℕ f)

-- TASK
-- Express < using ≤, without using _≡_
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- TASK
toℕ-< : {n : ℕ} → (x : Fin n) → toℕ x < n
toℕ-< Fin.zero = osuc ozero
toℕ-< (Fin.suc x) = osuc (toℕ-< x)

-- TASk
_ : 3 < 5
_ = osuc (osuc (osuc (osuc ozero)))

-- TASK
3NotLessThan2 : 3 < 2 → 𝟘
3NotLessThan2 (osuc (osuc ()))

-- TASK
<-suc : (n : ℕ) → n < suc n
<-suc zero = osuc ozero
<-suc (suc n) = osuc (<-suc n)

-- TASK
-- Convert from a ℕ to a Fin with an appropriate upper bound.
--
-- Note that (n : ℕ) → Fin n wouldn't work as a type, because, e.g.
-- we can't convert 0 to a Fin 0, because Fin 0 has no inhabitants.
--
-- We allow for an arbitrary m, instead of just Fin (suc n), because it's more convenient
-- (e.g. for fromℕ-toℕ-id)
fromℕ : ({m} n : ℕ) → n < m → Fin m
fromℕ zero (osuc x) = 0
fromℕ (suc n) (osuc x) = suc (fromℕ n x)

-- TASK
-- Prove that your conversions don't change the original ℕ
toℕ-fromℕ-id : (n : ℕ) → n ≡ toℕ (fromℕ n (<-suc n))
toℕ-fromℕ-id zero = refl
toℕ-fromℕ-id (suc n) = cong suc (toℕ-fromℕ-id n)

-- TASK
-- write down the calculated version of <
--
-- This is useful because later down the line we'll want to write Fins with as little boilerplate as possible.
-- If we combine Lt with fromℕ, we'll get a function where Agda can figure out the proof itself - see the fin function.
-- Lt : ℕ → ℕ → Set
-- Lt = {!!}

-- TASK
-- Prove that the calculated version implies the regular one,
-- so that we may provide the regular proof to fromℕ later.
Lt-< : (n m : ℕ) → Lt n m → n < m
Lt-< zero (suc m) ⟨⟩ = osuc ozero
Lt-< (suc n) (suc m) n<m = osuc (Lt-< n m n<m)

-- TASK
-- This is the "smart constructor" for Fins, which allows us to much more easily write "Fin literals" in our program.
--
-- The idea here is that if n and m are both known, since Lt is a function, Agda can calculate the Lt down to a One
-- or a 𝟘, and it can figure out how to fill in the One automatically, meaning that we can leave the Lt argument to be implicit
-- You'll need to expose *all* the implicit arguments here.
-- See the examples below.
fin : {m : ℕ} → (n : ℕ) → {Lt n m} → Fin m
fin {m} n {n<m} = fromNat {A = Fin m} {{NumFin {m}}} n {{n<m}}

_ : Fin 3
_ = fin 2
-- vs
_ : Fin 3
_ = fromℕ 2 (osuc (osuc (osuc ozero)))
-- vs
_ : Fin 3
_ = suc (suc (zero))
-- vs
_ : Fin 3
_ = 2

-- doesn't work, as expected, because 2 is not a Fin 2
-- _ : Fin 2
-- _ = fin 2

_ : Fin 5
_ = fin 2

_ : Fin 5
_ = fin 3

-- TASK
-- Increase the upper bound on a Fin.
-- This function is called "weaken", because we allow *more* values in the new Fin,
-- meaning we have *less* information about what the result actually is.
weakenFin : {m n : ℕ} → Fin n → n ≤ m → Fin m
weakenFin zero (osuc n≤m) = zero
weakenFin (suc f) (osuc n≤m) = suc (weakenFin f n≤m)

-- TASK
-- A specialised version of weakenFin, it is sometimes more convenient than the more general one.
weakenFinSuc : {n : ℕ} → Fin n → Fin (suc n)
weakenFinSuc {n} f = weakenFin {m = suc n} {n = n} f (≤-suc n)

-- TASK
<-≤ : {n m : ℕ} → n < m → n ≤ m
<-≤ {zero} {suc m} (osuc n<m) = ozero
<-≤ {suc n} {suc m} (osuc n<m) = osuc (≤-trans {n} {suc n} {m} (≤-suc n) n<m)

-- TASK
fromℕ-toℕ-id : {m n : ℕ} (f : Fin n) (p : n ≤ m) → f ≡ fromℕ (toℕ f) (toℕ-< f)
fromℕ-toℕ-id {suc m} {suc n} zero (osuc p) = refl
fromℕ-toℕ-id {suc m} {suc n} (suc f) (osuc p) = cong suc (fromℕ-toℕ-id f p)

-- TASK
-- Implement an equality check for two Fins with the same upper bound
decEqFin : {n : ℕ} → (x y : Fin n) → Dec (x ≡ y)
decEqFin {suc n} zero zero = yes refl
decEqFin {suc n} zero (suc y) = no (λ ())
decEqFin {suc n} (suc x) zero = no (λ ())
decEqFin {suc n} (suc x) (suc y) with decEqFin x y
... | no x≢y = no λ { refl → x≢y refl }
... | yes x≡y = yes (cong suc x≡y)

-- TASK
-- Implement the data type of nameless DeBruijn lambda terms,
-- parametrised by the number of variables in a particular term.
--
-- Some of the rest of the tasks rely on the names of these constructors, so don't change them.
data Lam (n : ℕ) : Set where
  var : (m : Fin n) → Lam n
  app : Lam n → Lam n → Lam n
  lam : Lam (suc n) → Lam n

-- TASK
-- Construct a variable from a ℕ directly.
-- You'll need to expose the implicit Lt argument.
--
-- This is a convenient prefix synonym for constructing nameless variables, allowing us to write
-- ` 4
-- instead of
-- var (fin 2)
-- or
-- var (suc (suc zero))
--
-- This, of course, only works when the m argument can be inferred.
` : {m : ℕ} → (n : ℕ) → {Lt n m} → Lam m
` n {x} = ?

-- TASK
-- Define the id function using nameless terms
lamId : Lam 0
lamId = lam (var 0)

-- TASK
-- Define the const function using nameless terms
-- taking two arguments, and always returning the first one.
lamK : Lam 0
lamK = lam (lam (var 1))

-- TASK
-- Implement the following function
s : {A B C : Set} → (A → B → C) → (A → B) → A → C
s g f x = (g x) (f x)

-- TASK
-- Translate the s function from above into Lam
lamS : Lam 0
lamS = lam (lam (lam (app (app (var 2) (var 0))
                          (app (var 1) (var 0)))))

-- TASK
-- Write the following lambda term as a nameless lambda term
-- λx. λy. x (u z)
-- \x → \y → x (u z)
_ : Lam 2
_ = lam (lam (app (var 1) (app (var 2) (var 3))))

-- NOTE
-- This withFree function is a syntactic "trick".
-- Oftentimes when we write a Lam term, we won't have the opportunity
-- to specify how many free variables it will have explicitly.
--
-- The result of this is that some of the constructors of lam, which have implicit arguments
-- based on the number of free variables, will not be able to infer these implicit arguments,
-- and we'll get some ambiguity errors.
--
-- As an example
-- lam (var zero)
-- could have as many free variables as we like - since the var zero is referring to the only
-- bound argument, this whole lambda term could have an arbitrary amount of free variables - even zero.
--
-- In order to resolve this, we'll be using withFree to be able to explicitly specify
-- the number of free variables on a function, by associating the first argument of withFree
-- as being the number of free varaibles in the second argument
--
-- Going back to the example from above
-- lam (var zero)
-- if we want to indicate taht this term will have 3 free variables, we would write
-- withFree 3 (lam (var zero))
-- Of course, we could also just explicitly specify one of the implicit arguments, i.e.
-- lam {3} (var zero)
-- but using withFree seems like a more consistent and clean approach.
withFree : (n : ℕ) → Lam n → Lam n
withFree _ x = x

_ :
  withFree 3 (lam (var 0))
  ≡
  lam (var 0)
_ = refl
-- vs
_ :
  lam {3} (var 0)
  ≡
  lam (var 0)
_ = refl

_ :
  lam {3} (var 0)
  ≡
  withFree 3 (lam (var 0))
_ = refl

-- An example of where Agda would get confused if we did not give it more type information
-- Uncomment this temporarily, to witness Agda's confusion:
-- _ :
--   lam (var zero)
--   ≡
--   lam (var zero)
-- _ = refl

-- TASK
dec≤ : (n m : ℕ) → Dec (n ≤ m)
dec≤ zero zero = yes ozero
dec≤ zero (suc m) = yes ozero
dec≤ (suc n) zero = no (λ ())
dec≤ (suc n) (suc m) with dec≤ n m
... | no n≰m = no λ { (osuc n≤m) → n≰m n≤m }
... | yes n≤m = yes (osuc n≤m)

-- TASK
dec< : (n m : ℕ) → Dec (n < m)
dec< zero zero = no (λ ())
dec< zero (suc m) = yes (osuc ozero)
dec< (suc n) zero = no (λ ())
dec< (suc n) (suc m) with dec< n m
... | no n≮m = no λ { (osuc n<m) → n≮m n<m }
... | yes n<m = yes (osuc n<m)

-- TASK
-- We'll want to eventually shift all the free variables in a lambda term by one.
-- However, in order to implement this, we'll need a helper function, which
-- has an additional argument to keep track of how many lambdas we've "gone into" during
-- our recursion.
--
-- Otherwise, we would have no way of knowing which variables are free and which are
-- actually bound by some outer lambda.
shiftUp1 : {n : ℕ} → ℕ → Lam n → Lam (suc n)
shiftUp1 c t = {!!}

-- TASK
-- Once we have shiftUp1, we can easily implement "shift all the free variables by one"
-- by using shiftUp1.
shiftUp10 : {n : ℕ} → Lam n → Lam (suc n)
shiftUp10 = ?

{-
-- TASK
-- what does shifting
-- λ 0
-- result in?
_ :
  withFree 1 (shiftUp10 (lam (` 0)))
  ≡
  {!!}
_ = refl

-- TASK
-- what does shifting
-- λ λ 1
-- result in?
_ :
  shiftUp10 (withFree 2 (lam (lam (` 1))))
  ≡
  {!!}
_ = refl

-- TASK
-- what does shifting
-- λ λ 3
-- result in?
_ :
  shiftUp10 (withFree 4 (lam (lam (` 3))))
  ≡
  {!!}
_ = refl

-- TASK
-- what does shifting
-- λ λ (0 (0 2)
-- result in?
_ :
  shiftUp10 (withFree 4 (lam (lam (app (` 1) (app (` 0) (` 2))))))
  ≡
  {!!}
_ = refl

-- TASK
-- Implement substitution, i.e.
-- t [ x => p ]
-- should be the result of replacing all x's in t with a p.
_[_=>_] : {n : ℕ} → Lam n → Fin n → Lam n → Lam n
_[_=>_] = {!!}

-- TASK
-- What does substituting 2 for 3 in 1 result in?
--
-- note that we have to give our lambda term enough free vars
-- for the substitution to be applicable, even if we're not using them!
_ :
  withFree 4 ((` 1) [ fin 2 => ` 3 ])
  ≡
  {!!}
_ = refl

-- TASK
-- What does substituting 2 for 3 in 2 result in?
_ :
  withFree 4 ((` 2) [ fin 2 => ` 3 ])
  ≡
  {!!}
_ = refl

-- TASK
-- What does substituting 2 for 3 in λ0 result in?
_ :
  withFree 4 (lam (` 0) [ fin 2 => ` 3 ])
  ≡
  {!!}
_ = refl

-- TASK
-- what does substituting 3 for 5 in λ3 result in?
_ :
  withFree 6 (lam (` 3)) [ fin 2 => ` 5 ]
  ≡
  {!!}
_ = refl

-- TASK
-- what does substituting 0 for 01 in λ0 result in?
_ :
  withFree 4 (lam (` 0)) [ fin 0 => app (` 0) (` 1) ]
  ≡
  {!!}
_ = refl

-- TASK
-- what does substituting 0 for λ01 in 0(λ01) result in?
_ :
  withFree 2 (app (` 0) (lam (app (` 0) (` 1)))) [ fin 0 => lam (app (` 0) (` 1)) ]
  ≡
  {!!}
_ = refl

-- TASK
-- Define named lambda terms.
-- We could use strings here, for variable names, but instead we'll use ℕs, in the sense that
-- 1 will "stand for" x1, 8 for x8, etc.
--
-- The only reason for doing this is so that we can avoid having to introduce strings.
data NamedLam : Set where
  var : ℕ → NamedLam
  app : NamedLam → NamedLam → NamedLam
  lam_>_ : ℕ → NamedLam → NamedLam

-- TASK
-- Convert a nameless lambda term to a named one, using a context of
-- an appropriate type
name : ? → Lam ? → NamedLam
name ctxt t = {!!}
-}
