module Homework.Selections.Selections where

open import Lib.Zero using (𝟘; ¬_; zero-elim)
open import Lib.One using (𝟙; ⟨⟩)
open import Lib.Two using (𝟚; tt; ff)
open import Lib.Nat using (ℕ; zero; suc; ozero; osuc; _<_; _≤_; ≤-suc; ≤-trans; +-right-suc)
open import Lib.Sigma using (Σ; _,_; fst; snd; _*_)
open import Lib.Vec using (Vec; []; _∷_)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

-- Implement less than or equal for nats, but in a different way,
-- which will also turn out to be convenient for selecting elements
-- from vectors, based on their indices
data _<S=_ : ℕ → ℕ → Set where
  -- zero should be ≤ zero, or alternatively,
  -- we can select the empty vec from the empty vec
  o-zero : 0 <S= 0
  -- we should have some way to add sucs on the right, without making the
  -- left number bigger, so that we can prove stuff like 3 <S= 5, or alternatively
  -- we can skip selecting the head of a vector
  o-skip : {n m : ℕ} → n <S= m → n <S= suc m
  -- if n ≤ m, then suc n ≤ suc m, or alternatively,
  -- we select the head of the vector
  o-succ : {n m : ℕ} → n <S= m → suc n <S= suc m

-- TASK
-- some positive unit tests
_ : 1 <S= 1
_ = o-succ o-zero

_ : 1 <S= 3
_ = o-skip (o-skip (o-succ o-zero))

_ : 3 <S= 5
_ = o-skip (o-skip (o-succ (o-succ (o-succ o-zero))))

-- TASK
-- In general there's more than one way in which n <S= m.
-- Prove it for n = 1 and m = 2
_ :
  Σ (1 <S= 2) \p → -- there's a proof p for 1 <S= 2
  Σ (1 <S= 2) \q → -- and a proof q for 1 <S= 2
  ¬ (p ≡ q)        -- and they're different
_ = o-skip (o-succ o-zero) , o-succ (o-skip o-zero) , λ ()

-- It might be interesting to try to figure out how many proofs there are for n <S= m, for fixed n and m.
--
-- You can use -l in a hole for such a proof (e.g. _ : 1 <S= 4; _ = ?),
-- together with Agdas auto, to get it to list all of them.

-- TASK
-- Prove that 0 is <S= any number
-- Alternatively, this represents the "empty" selection - it selects nothing.
0<S= : (n : ℕ) → 0 <S= n
0<S= zero = o-zero
0<S= (suc n) = o-skip (0<S= n)

-- TASK
-- Prove that <S= is reflexive.
-- Alternatively, this is the selection that selects all the elements of a vector
-- similarly, we can have an "all" sub - it selects everything
-- or alternatively, a reflexivity proof
--
-- This is referred to as "the identity selection".
refl-<S= : (n : ℕ) → n <S= n
refl-<S= zero = o-zero
refl-<S= (suc n) = o-succ (refl-<S= n)

-- TASK
-- For any number, the proof that 0 is Leq to it is unique - and that's
-- the one you already implemented, i.e. 0<S=.
--
-- This may seem like a weird thing to prove, but it pops up
-- later on, when proving properties about vector selections
0<S=-unique : {n : ℕ} (p : 0 <S= n) → 0<S= n ≡ p
0<S=-unique o-zero = refl
0<S=-unique (o-skip p) = cong o-skip (0<S=-unique p)

-- TASK
-- We can convert our usual ≤ to a selection
≤-<S= : {n m : ℕ} → n ≤ m → n <S= m
≤-<S= {.zero} {m} ozero = 0<S= m
≤-<S= {.(suc _)} {.(suc _)} (osuc x) = o-succ (≤-<S= x)

-- TASK
-- and vice versa
<S=-≤ : {n m : ℕ} → n <S= m → n ≤ m
<S=-≤ {.0} {.0} o-zero = ozero
<S=-≤ {n} {suc m} (o-skip x) = ≤-trans (<S=-≤ x) (≤-suc m)
<S=-≤ {.(suc _)} {.(suc _)} (o-succ x) = osuc (<S=-≤ x)

-- TASK
-- The actual function that does the selection.
-- The idea here is to use the proof of n <S= m to guide you on how to
-- carve out a vector of size n from the input vector of size m
select : {A : Set} {m n : ℕ} → n <S= m → Vec A m → Vec A n
select o-zero [] = []
select (o-skip n<S=m) (x ∷ xs) = select n<S=m xs
select (o-succ n<S=m) (x ∷ xs) = x ∷ select n<S=m xs

-- TASK
-- We can compose selections.
-- Alternatively, this is transitivity for _<S=_.
-- You should strive to make this as lazy as possible in its pattern matches (so as few matches as possible)
-- so that your later proofs are easier.
_S<<_ : {n m k : ℕ} → n <S= m → m <S= k → n <S= k
-- o-zero S<< q = q
-- o-skip p S<< o-skip q = o-skip (o-skip p S<< q)
-- o-skip p S<< o-succ q = o-skip (p S<< q)
-- o-succ p S<< o-skip q = o-skip (o-succ p S<< q)
-- o-succ p S<< o-succ q = o-succ (p S<< q)
p S<< o-zero = p
p S<< o-skip q = o-skip (p S<< q)
o-skip p S<< o-succ q = o-skip (p S<< q)
o-succ p S<< o-succ q = o-succ (p S<< q)

-- TASK
-- Selecting a composition of selections is the same as composing invocations of the select function
select-S<< :
  {A : Set} {n m k : ℕ}
  (p : n <S= m) (q : m <S= k) (xs : Vec A k) →
  select (p S<< q) xs ≡ select p (select q xs)
select-S<< o-zero o-zero [] = refl
select-S<< o-zero (o-skip q) (x ∷ xs) = select-S<< o-zero q xs
select-S<< (o-skip p) (o-skip q) (x ∷ xs) = select-S<< (o-skip p) q xs
select-S<< (o-skip p) (o-succ q) (x ∷ xs) = select-S<< p q xs
select-S<< (o-succ p) (o-skip q) (x ∷ xs) = select-S<< (o-succ p) q xs
select-S<< (o-succ p) (o-succ q) (x ∷ xs) = cong (x ∷_) (select-S<< p q xs)

-- TASK
-- Composing selections with the identity selection does nothing, i.e.
-- it's a left and right identity.
S<<-left-id : {n m : ℕ} (p : n <S= m) → (refl-<S= n S<< p) ≡ p
S<<-left-id o-zero = refl
S<<-left-id (o-skip p) = cong o-skip (S<<-left-id p)
S<<-left-id (o-succ p) = cong o-succ (S<<-left-id p)

S<<-right-id : {n m : ℕ} (p : n <S= m) → (p S<< (refl-<S= m)) ≡ p
S<<-right-id o-zero = refl
S<<-right-id (o-skip p) = cong o-skip (S<<-right-id p)
S<<-right-id (o-succ p) = cong o-succ (S<<-right-id p)


-- TASK
-- Selection composition is associative
S<<-assoc :
  {n m k v : ℕ} (p : n <S= m) (q : m <S= k) (t : k <S= v) →
  (p S<< q) S<< t ≡ p S<< (q S<< t)
S<<-assoc p          q          o-zero     = refl
S<<-assoc p          q          (o-skip t) = cong o-skip (S<<-assoc p q t)
S<<-assoc p          (o-skip q) (o-succ t) = cong o-skip (S<<-assoc p q t)
S<<-assoc (o-skip p) (o-succ q) (o-succ t) = cong o-skip (S<<-assoc p q t)
S<<-assoc (o-succ p) (o-succ q) (o-succ t) = cong o-succ (S<<-assoc p q t)

-- TASK
-- We can use selections of a particular form to index into a vector
-- A selection with 1 on the left effectively means that there is only one place
-- in its construction that can have the o-succ constructor.
--
-- That's *exactly* the index of the item we want to get from the vector
-- There're som examples below that might be useful to look at.
vProject : {A : Set} {n : ℕ} → Vec A n → 1 <S= n → A
vProject (x ∷ xs) (o-skip s) = vProject xs s
vProject (x ∷ xs) (o-succ s) = x

-- Note the locations of the "up arrows"
_ : vProject (0 ∷ 1 ∷ 2 ∷ []) (o-succ (o-skip (o-skip o-zero))) ≡ 0
--            ^                  ^
_ = refl

_ : vProject (0 ∷ 1 ∷ 2 ∷ []) (o-skip (o-succ (o-skip o-zero))) ≡ 1
--                ^                      ^
_ = refl

_ : vProject (0 ∷ 1 ∷ 2 ∷ []) (o-skip (o-skip (o-succ o-zero))) ≡ 2
--                    ^                          ^
_ = refl

-- TASK
-- We can also do the opposite.
-- If for every value of (1 <S= n) we can get back an A, we can use those values
-- to reconstruct back a vector
vTabulate : {A : Set} (n : ℕ) → (1 <S= n → A) → Vec A n
vTabulate zero extract = []
vTabulate (suc n) extract = extract (o-succ (0<S= n)) ∷ vTabulate n λ { s → extract (o-skip s) }

-- ix : ({n} i : ℕ) → {1 ≤ n} → {i < n} → (1 <S= n)
-- ix {suc n} zero = {! !}
-- ix {suc n} (suc i) = {! !}

-- TASK
-- Tabulating projections should result in the original vector
vTabulate-vProject : {A : Set} {n : ℕ} → (xs : Vec A n) → vTabulate n (vProject xs) ≡ xs
vTabulate-vProject [] = refl
vTabulate-vProject (x ∷ xs) = cong (x ∷_) (vTabulate-vProject xs)

-- TASK
-- Projecting a tabulation should result in the original tabulation
vProject-vTabulate :
  {A : Set} {n : ℕ}
  (f : 1 <S= n → A) (i : 1 <S= n) →
  vProject (vTabulate n f) i ≡ f i
vProject-vTabulate {n = suc n} f (o-skip i) = vProject-vTabulate {n = n} (λ { s → f (o-skip s) }) i
vProject-vTabulate f (o-succ i) = cong f (cong o-succ (0<S=-unique i))
