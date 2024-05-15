module Joro.SixLive where

-- open import Lib.List
-- open import Lib.Dec
-- open import Lib.Eq
-- open import Lib.ℕ
-- open import Lib.Sum
-- open import Lib.𝟙
-- open import Lib.𝟘
-- open import Lib.Sigma
-- open import Lib.Fun

open import Lib.Zero using (𝟘)
open import Lib.One using (𝟙; ⟨⟩)
open import Lib.Two using (𝟚)
open import Lib.Nat using (ℕ; zero; suc; ozero; osuc; _≤_; +-right-suc)
open import Lib.Sum using (_+_; inl; inr)
open import Lib.Sigma using (Σ; _,_)
open import Lib.Decidable using (Dec; no; yes)
open import Lib.List using (List; []; _,-_; length)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

-- * LeftistHeap and Selections hws
-- * Lib.Fun with flip
-- * modules

--module Lists (A : Set) where
--
--  +L-assoc' : (xs ys zs : List A) → List A
--  +L-assoc' xs _ _ = xs
--
--  reverse-swap' : (xs ys : List A) → List A
--  reverse-swap' xs _ = xs


-- open Lists renaming (+L-assoc' to peshogosho)
--
-- foo : (A : Set) → (xs ys zs : List A) → List A
-- foo = peshogosho
--
-- _ : peshogosho ℕ (1 ,- []) [] [] ≡ (1 ,- [])
-- _ = refl



-- * BST:
-- explain we're going to use Leqℕ to make writing trees easier
-- (also should be better for perf theoretically)
--
-- interactively try a "naive" version of BST
-- note how for List → BST it doesn't work well
--
-- suggest "loosening constraints" solution in this case
-- implement Bound, LeqBound, BST
-- mention "pushing down constraints" and show tree diagram
--          2
--       1  .  3
--     ≤.≤.≤.≤
--       .  .  .
-- -inf≤1≤2≤3≤+inf

-- TASK
-- Implement the "calculated" version of ≤, i.e.
-- do pattern matching on the inputs to determine what the result type is.
Leqℕ : ℕ → ℕ → Set
Leqℕ zero m = 𝟙
Leqℕ (suc _) zero = 𝟘
Leqℕ (suc n) (suc m) = Leqℕ n m

_ : 3 ≤ 5
_ = osuc (osuc (osuc ozero))

_ : Leqℕ 3 5
_ = ⟨⟩

-- TASK
-- Compare two numbers - it should be the case that we
-- either have n ≤ m or m ≤ n
decLeqℕ : (n m : ℕ) → Leqℕ n m + Leqℕ m n
decLeqℕ zero m = inl ⟨⟩
decLeqℕ (suc n) zero = inr ⟨⟩
decLeqℕ (suc n) (suc m) = decLeqℕ n m

-- TASK
-- Convert from _≤_ to Leqℕ
≤-Leqℕ : {n m : ℕ} → n ≤ m → Leqℕ n m
≤-Leqℕ ozero = ⟨⟩
≤-Leqℕ (osuc x) = ≤-Leqℕ x

module
  Sorting
    (Key : Set)
    (Leq : Key → Key → Set)
    (_≤?_ : (x y : Key) → Leq x y + Leq y x)
  where

  data Bound : Set where
    -inf : Bound
    inKey : Key → Bound
    +inf : Bound

  LeqBound : Bound → Bound → Set
  LeqBound -inf y = 𝟙
  LeqBound (inKey x) (inKey y) = Leq x y
  {-# CATCHALL #-}
  LeqBound x +inf = 𝟙
  {-# CATCHALL #-}
  LeqBound _ _ = 𝟘

  -- -inf<_ : Key → Set
  -- -inf< k = LeqBound -inf (inKey k)

  data BST (lo hi : Bound) : Set where
    empty : LeqBound lo hi → BST lo hi
    node : (x : Key) (l : BST lo (inKey x)) (r : BST (inKey x) hi) → BST lo hi

  -- TASK
  -- We'll be implementing sorting of Lists by doing the following
  -- 1. We'll define a type of ordered lists (OList), similar to BST
  -- 2. We'll define a function to go from a List to a BST
  -- 3. We'll define a function to go from a BST to an OList
  --
  -- In this way, we'll get sorting that's (almost) correct by oconstruction,
  -- since we'll define OLists thanks to 1.
  -- The "actual" sorting will happen in the intermediate step

  -- TASK
  -- Implement insertion into a BST
  -- You'll need to use _≤?_ to compare two values
  -- The ? in the signature is left there for you to fill in with the appropriate
  -- oconstraints that you think you'll need.
  insert :
    {lo hi : Bound} (k : Key) →
    LeqBound lo (inKey k) → LeqBound (inKey k) hi →
    BST lo hi → BST lo hi
  insert k l r (empty p) = node k (empty l) (empty r)
  insert k l r (node x bustₗ bustᵣ) with k ≤? x
  ... | inl p = node x (insert k l p bustₗ) bustᵣ
  ... | inr p = node x bustₗ (insert k p r bustᵣ)

  -- TASK
  -- Implement converting an ordinary list to a BST
  -- Note how the BST is unbounded, so that it's easier for us to implement this.
  listToBST : List Key → BST -inf +inf
  listToBST [] = empty ⟨⟩
  listToBST (x ,- xs) = insert x ⟨⟩ ⟨⟩ (listToBST xs)

  -- TASK
  -- Use the same idea as in BST to define "ordered lists"
  -- Be careful about what oconstraints you need in your recursive case!
  data OList (lo hi : Bound) : Set where
    [] : {LeqBound lo hi} → OList lo hi
    _,-_ : (n : Key) → {LeqBound lo (inKey n)} → OList (inKey n) hi → OList lo hi

  olist-weaken : {lo₁ lo₂ hi : Bound} → LeqBound lo₂ lo₁ → OList lo₁ hi → OList lo₂ hi
  olist-weaken p [] = [] {?} {?} {?}
  olist-weaken p (n ,- xs) = {! !}

  -- TASK
  -- You should be able to represent an ordered list as an OList
  -- Scroll down to OList_UNIT_TESTS_SUCCESS and try to write out
  -- * []
  -- * [1,2,3]
  -- * [1,5,9]
  -- as OLists

  -- _ : OList -inf +inf
  -- _ = []

  -- _ : OList -inf +inf
  -- _ = 1 ,- 2 ,- 3 ,- []

  -- TASK
  -- You should not be able to represent a list that is not ordered as an OList
  -- Scroll down to OList_UNIT_TESTS_FAILURE and verify that you cannot write out
  -- * [2, 1]
  -- * [4, 5, 1]
  -- as OLists

  -- TASK
  -- Implement the flattenBST operation, which converts a BST into an OList.
  -- You'll most likely need an additional function to implement flattenBST -
  -- think about what *exactly* it needs to be and implement it.

  flattenBST : {lo hi : Bound} → BST lo hi → OList lo hi
  flattenBST {lo} {hi} (empty x) = [] {lo} {hi} {x}
  flattenBST {lo} {hi} (node x bustₗ bustᵣ) = flattenBST bustₗ +OL (x ,- flattenBST bustᵣ)
    where
      _+OL_ : {lo₁ hi₁ lo₂ hi₂ : Bound} (xs : OList lo₁ hi₁) (ys : OList lo₂ hi₂) → OList lo₁ hi₂
      [] +OL ys = ?
      (n ,- xs) +OL ys = {! !}

{-
  -- TASK
  -- Finally, we can sort lists by composing flattenBST and listToBST
  sort : List Key → OList -inf +inf
  sort = ?

  -- (OPTIONAL) TASK
  -- This sorting actually directly "corresponds" to a very well
  -- known sorting algorithm.
  -- "Corresponds" here means that it's doing basically the same operations -
  -- comparisons and building the list back up -
  -- as the algorithm in question.
  --
  -- Can you guess which algorithm that is?

  -- TASK
  -- "Forget" that a list was sorted
  OListForget : {lo hi : Bound} → OList lo hi → List Key
  OListForget = ?

  -- TASK
  -- Sort a list without keeping the proof that you sorted it
  -- Useful for tests
  --
  -- Scroll down to sortFroget_UNIT_TESTS
  -- to run some unit tests that your sorting actually sorts
  sortForget : List Key → List Key
  sortForget = ?
-}

-- We can now open the Sorting module so that we can show some example invocations/
-- unit tests for sorting
open Sorting ℕ Leqℕ decLeqℕ

-- _ : BST' 3 5
-- _ = node 4 (empty <>) (empty <>)
-- -- LeqBound 3 4 → 𝟙
--
--
-- _ : BST' 3 5
-- _ = node 8 (empty <>) (empty {! !})
-- LeqBound 3 8 → 𝟙
-- LeqBound 8 5 → 𝟘

-- UNIT TESTS

-- OList_UNIT_TESTS_SUCCESS
-- []
_ : OList -inf +inf
_ = []

-- [1, 2, 3]
_ : OList (inKey 1) (inKey 3)
_ = 1 ,- 2 ,- 3 ,- []

-- [1, 5, 9]
_ : OList -inf +inf
_ = 1 ,- 5 ,- 9 ,- []

-- OList_UNIT_TESTS_FAILURE

-- [2, 1]
_ : OList -inf +inf
_ = 2 ,- (_,-_ 1 {?} ([] {inKey 1}))

-- [4, 5, 1]
_ : OList -inf +inf
_ = ?

{-
-- sortFroget_UNIT_TESTS
_ : sortForget [] ≡ []
_ = refl

_ : sortForget (5 ,- 3 ,- 8 ,- 10 ,- []) ≡ (3 ,- 5 ,- 8 ,- 10 ,- [])
_ = refl

_ : sortForget (11 ,- 3 ,- 5 ,- 3 ,- 8 ,- 10 ,- []) ≡ (3 ,- 3 ,- 5 ,- 8 ,- 10 ,- 11 ,- [])
_ = refl
-}

-- "Syntax sugar" to allow us to write single element lists
[_] : {A : Set} → A → List A
[ x ] = x ,- []

infix 100 [_]

{-

-- use a module to introduce some "local variable" types,
-- so we don't have to repeat them over and over in the definitions below
module Splits (A : Set) where

  -- xs <[ ys ]> zs
  -- expresses the fact that you can combine xs and zs to get ys,
  -- without changing the original order of elements, i.e.
  -- xs and zs are both sublists of ys, and together, they contain all of the elements
  -- of ys.
  data _<[_]>_ : List A → List A → List A → Set where
    -- you can combine two empty lists to get an empty list
    sz : [] <[ [] ]> []

    -- if you can combine l and r into m
    -- then you can also add an element onto l and onto m at the same time
    sl : {l m r : List A} {x : A} →
      l        <[ m        ]> r →
      (x ,- l) <[ (x ,- m) ]> r

    -- if you can combine l and r into m
    -- then you can also add an element onto r and onto m at the same time
    sr : {l m r : List A} {x : A} →
      l <[ m        ]> r →
      l <[ (x ,- m) ]> (x ,- r)

  infix 10 _<[_]>_

  -- TASK
  -- Construct the split that puts everything on the left
  left-split : (xs : List A) → xs <[ xs ]> []
  left-split = ?

  -- TASK
  -- Construct the split that puts everything on the right
  right-split : (xs : List A) → [] <[ xs ]> xs
  right-split = ?

  -- TASK
  -- If a lists splits (on the left) entirely into another, then they are equal
  inv-left-split : {xs ys : List A} → xs <[ ys ]> [] → xs ≡ ys
  inv-left-split = ?

  -- TASK
  -- If a lists splits (on the right) entirely into another, then they are equal
  inv-right-split : {xs ys : List A} → [] <[ xs ]> ys → xs ≡ ys
  inv-right-split = ?

  -- TASK
  -- If a list splits entirely into another, the inverse is also true
  shuf-empty-split : {xs ys : List A} → xs <[ ys ]> [] → [] <[ xs ]> ys
  shuf-empty-split = ?

  -- TASK
  -- We can swap the places of a splitting
  split-swap : {xs ys zs : List A} → xs <[ ys ]> zs → zs <[ ys ]> xs
  split-swap = ?

  -- TASK
  -- Adding two lists together results in a split of the two lists
  +L-split : (xs ys : List A) → xs <[ xs +L ys ]> ys
  +L-split = {! !}

  -- TASK
  -- Recursively define what it should mean for all of the elements
  -- of a list to satisfy some predicate.
  -- HINT: Try to recall how we expressed "the proof for A and B", given that we have
  -- "the proof for A" and "the proof for B"
  All : (A → Set) → List A → Set
  All = {! !}

  -- TASK
  -- Given a decidable predicate and a list, produce two lists
  -- one with all the elements for which the predicate holds
  -- and one with all the elements for which it doesn't,
  -- which are a splitting of the original input list.
  partition :
    {P : A → Set} →
    ((x : A) → Dec (P x)) →
    (xs : List A) →
      {! !}
  partition = {! !}

  -- xs ~ ys
  -- expresses the fact that xs is a permutataion of ys
  data _~_ : List A → List A → Set where

    -- [] is a permutation of []
    nil : [] ~ []

    -- if xs is a permutation of ys, then (x ,- xs) is a permutation
    -- of the list you get by inserting x somewhere into ys
    lcons :
      {xs ys ys' : List A} {x : A} →
      [ x ] <[ ys' ]> ys →
      xs ~ ys →
      (x ,- xs) ~ ys'


  -- TASK
  -- Prove that any list is a permutation of itself
  ~-refl : (xs : List A) → xs ~ xs
  ~-refl = ?

  -- TASK
  -- Implement a more symmetric version of lcons, i.e.
  -- if we have
  -- xs ~ ys
  -- lcons only allows us to put things at the head of xs,
  -- but it will be convenient to be able to put things anywhere inside of xs.
  --
  -- This is a fairly complex thing, if you're feeling stuck, look at switch-split-lefts
  -- below, which is the function I personally derived entirely from the place where
  -- I was stuck here.
  consP :
    {xs xs' ys ys' : List A} {z : A} →
    -- if we know z can be combined with xs to make xs'
    [ z ] <[ xs' ]> xs →
    -- and we know z can be combined with ys to make ys'
    [ z ] <[ ys' ]> ys →
    -- and we know that xs is a permutation of ys
    xs ~ ys →
    -- then we know that xs' is a permutation of ys'
    xs' ~ ys'
  consP = ?

  -- TASK
  -- Given two splittings, one of which is a "part" of the other,
  -- we want to do some reshuffling/rotation of this form:
  --
  -- Input:
  --     ys1
  -- xs1     ys2
  --     xs2     zs2
  -- ≡≡≡≡≡>
  -- Output:
  --     ys1
  -- xs2     spl
  --     xs1     zs2
  -- The important bit for us here is that we now get
  -- xs2 <[ ys1 ]> ....
  -- This is *one possible way* to help with implementing the consP operation.
  --
  -- Also, I didn't have time to prove this myself, so it's entirely possible
  -- this is also crazy hard, but it should be doable
  switch-split-lefts :
    {xs1 ys1 ys2 xs2 zs2 : List A} →
     xs1 <[ ys1 ]> ys2 →
     xs2 <[ ys2 ]> zs2 →
       List A >< \spl →
         xs2 <[ ys1 ]> spl *
         xs1 <[ spl ]> zs2
  switch-split-lefts = ?
-}

  -- TODO: add more permutation tasks here?
  -- we want to do find left on right, transitivity, symmetry, action on All
