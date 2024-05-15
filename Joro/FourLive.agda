module Joro.FourLive where

open import Lib.Zero using (𝟘)
open import Lib.One using (𝟙)
open import Lib.Two using (𝟚)
open import Lib.Nat using (ℕ; zero; suc) renaming (_+_ to _+N_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
module HASK = Category HASK
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_])
open import Project.Control.Monad using (Monad)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)
open import Project.Postulates using (funext)

open import Project.Data.Const using (Const; constᶠ; constFunctor)

open import Lib.Utils renaming (_∘_ to _∘ₐ_)

-- TODO: mention Bins homework

-- TODO: mention new additions to libs:
-- new lemmas in Nat, <= in nat +N lemmas for <=

-- TODO: hide eq import for now, enable after finishing demonstrations
-- TODO: new eq definition
-- old:
-- data _≡_ {A : Set} : A → A → Set where
--   refl : (x : A) → x ≡ x
-- 1. Note how often we don't need to give the arg to refl, as witnessed by students. TODO: example
--    This is because when you have the type x ≡ x, agda can clearly already infer what the arg is
--    Hence, we can make it implicit.
-- data _≡_ {A : Set} : A → A → Set where
--   refl : {x : A} → x ≡ x
-- TODO: example
-- 2. Note how because it is now implicit, and is present in all the constructors of _≡_, we can also make it a param instead.
-- data _≡_ {A : Set} {x : A} : A → Set where
--   refl : x ≡ x
-- Remind how params work.
-- TODO: example of new refl usage in a simple case, and in a recursive proof
-- Note that we only had an explicit Eq so far for simplicity and to make it clearer what's going on when we're writing refl.

-- Show +-commut to serve as a motivating example:
-- +-commut' : (n m : ℕ) → n +N m ≡ m +N n
-- +-commut' zero m = ≡-symm (+-right-zero m)
-- +-commut' (suc n) m = ≡-trans (suc $= +-commut' n m) (+-right-suc m n)
-- 1. Introduce rewrite as a construct which allows us to use an equality to "rewrite all occurences of the left side to the right side".
--    Give a step by step example on +-commut', using rewrites instead.
--    Note how rewrite is not symmetric - it only "rewrites" the left side to the right side, and not vice versa.
--    A good example for this is the fact that we need to use
--      rewrite ≡-symm (+-right-suc m n)
--    and just
--      rewrite +-right-suc m n
--    doesn't do anything
--    Show that you can stack multiple rewrites one after the other in the recursive case.
--    End goal:
--      +-commut' : (n m : ℕ) → n +N m ≡ m +N n
--      +-commut' zero m rewrite +-right-zero m = refl
--      +-commut' (suc n) m rewrite ≡-symm (+-right-suc m n) rewrite +-commut' n m = refl
-- 2. rewrite is very nice for proving, but it has the issue of being hard to decipher afterwards - it's not very clear
--    what the proof is. It has the issue of the order of transformations not being clear, and it not being clear what we're transforming.
--    We can fix both of these issues with some clever operators.
--    Recall the ≡-trans definition.
--    Bring forth the suggestion of introducing an operator form for ≡-trans, to allow for more readable chaining, e.g.:
--      _//≡_ :
--        {A : Set} {x y z : A} →
--        x ≡ y →
--        y ≡ z →
--        x ≡ z
--      _//≡_ = ≡-trans
--      infixr 10 _//≡_
--    Now add a new +-commut which uses _//≡_ instead of ≡-trans
--    We can now easily chain a lot of ≡-trans without caring about parens, but the intermediate steps of the proof are still not clear -
--    in the chain x ≡ y, y ≡ z, z ≡ u, we only know what x and u are, due to the end goal, but we don't really know much about y and z.
--    To remedy this, we can make one of the params of _//≡_ explicit, so that at each step, we can see what exactly the term we're transforming is.
--      _=[_]_ :
--        {A : Set} {y z : A}
--        (x : A) →
--        x ≡ y →
--        y ≡ z →
--        x ≡ z
--      _ =[ p ] q = ≡-trans p q
--      infixr 10 _=[_]_
--    We'll also add an explicit version of refl, so that we can also explicitly mention our final term:
--      _QED : {A : Set} (x : A) → x ≡ x
--      _ QED = refl
--      infix 11 _QED
--    Use this definition to show +-commut again, step by step. First, note how you can always start a proof by writing out one usage of _=[_]_ and _QED,
--    with your initial and final terms:
--      +-commut''' zero m =
--        m =[ {! !} ]
--        m +N zero QED
--    Also note that if you leave the holes empty like so:
--      +-commut''' zero m =
--        ? =[ {! !} ]
--        ? QED
--    You can almost always use the auto command to fill them in, because agda knows what they are.
--    Finish the proof for the base case.
--      +-commut''' zero m =
--        m =[ ≡-symm (+-right-zero m) ]
--        m +N zero QED
--    Repeat the same initial steps for the recursive case:
--        +-commut''' (suc n) m =
--          suc (n +N m) =[ {! !} ]
--          m +N suc n QED
--    Now we can demonstrate how we can easily add additional _=[_]_ calls to extend our proof.
--      +-commut''' (suc n) m =
--        suc (n +N m) =[ {! !} ]
--        {! !} =[ {! !} ]
--        m +N suc n QED
--    Note how we can either choose to
--    1. first fill in the first hole if we know what lemma we're using
--    2. or we can choose to first fill in the second hole, if we know what term we want to achieve
--    3. or we can even choose to fill in the last hole, if we know what lemma we want to use at the end.
--    Note how, again, if we fill in one of the lemmas, agda can once again automatically fill in the term hole.
--    Proceed to write the finished version:
--      +-commut''' (suc n) m =
--        suc (n +N m) =[ suc $= +-commut''' n m ]
--        suc (m +N n) =[ +-right-suc m n ]
--        m +N suc n QED
--    Stop at this moment, and make sure that students understand how exactly the fixities work. A good idea is to
--    explicitly put all the parens on all the expressions, so that it's very clear what each operator is applied to.
--    Explicitly mention how _QED is a postfix operator which binds more tightly compared to _=[_], so we don't need to put parens there.
--    Explicitly mention _=[]_ which we can use for our own convenience to write two terms which are definitionally equal.
--

-- TASK
-- Implement a linear and constant space tail recursive version of ℕ addition
addNat : ℕ → ℕ → ℕ
addNat zero m = m
addNat (suc n) m = addNat n (suc m)

-- TASK
-- Prove that your addNat behaves like +N.
-- Think about what lemma you'll need to formulate for the recursive case.
addNat-≡-+ : (n m : ℕ) → addNat n m ≡ n +N m
addNat-≡-+ zero m = refl
addNat-≡-+ (suc n) m =
  begin
    addNat (suc n) m
  ∼⟨ lemma1 n m ⟩
    suc (addNat n m)
  ∼⟨ cong suc (addNat-≡-+ n m) ⟩
    suc (n +N m)
  ∼⟨ symmetric lemma2 ⟩
    suc n +N m
  ∎
  where
    lemma1 : (n m : ℕ) → addNat (suc n) m ≡ suc (addNat n m)
    lemma1 zero m = refl
    lemma1 (suc n) m = lemma1 n (suc m)

    lemma2 : suc n +N m ≡ suc (n +N m)
    lemma2 = refl

-- Traditionally defined recursive lists, parametrised by the type of elements in them.
data List (a : Set) : Set where
  -- the empty list is a list
  [] : List a
  -- we can add a new element to the "head" of a list
  _,-_ : a → List a → List a

infixr 21 _,-_

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ,- xs) = f x ,- map f xs

mapId : {A : Set} (xs : List A) → map HASK.id xs ≡ xs
mapId [] = refl
mapId (x ,- xs) =
  begin
    map HASK.id (x ,- xs)
  ∼⟨⟩
    x ,- map HASK.id xs
  ∼⟨ cong (x ,-_) (mapId xs) ⟩
    x ,- xs
  ∎

mapHomomorphism : {A B C : Set} (f : A → B) (g : B → C) (xs : List A) → map g (map f xs) ≡ map (g ∘ₐ f) xs
mapHomomorphism f g [] = refl
mapHomomorphism f g (x ,- xs) =
  begin
    map g (map f (x ,- xs))
  ∼⟨⟩
    g (f x) ,- map g (map f xs)
  ∼⟨ cong (g (f x) ,-_) (mapHomomorphism f g xs) ⟩
    g (f x) ,- map (λ x₁ → g (f x₁)) xs
  ∼⟨⟩
    map (g ∘ₐ f) (x ,- xs)
  ∎

mapHomomorphism2 : {A B C : Set} {f : A → B} {g : B → C} (xs : List A) → map (g ∘ₐ f) xs ≡ map g (map f xs)
mapHomomorphism2 {f = f} {g = g} [] = refl
mapHomomorphism2 {f = f} {g = g} (x ,- xs) =
  begin
    map (g ∘ₐ f) (x ,- xs)
  ∼⟨⟩
    g (f x) ,- map (λ x₁ → g (f x₁)) xs
  ∼⟨ cong (g (f x) ,-_) (mapHomomorphism2 {f = f} {g = g} xs) ⟩
    g (f x) ,- map g (map f xs)
  ∼⟨⟩
    map g (map f (x ,- xs))
  ∎

listFunctor : HomFunctor HASK
listFunctor = record
  { F[_] = List
  ; fmap = map
  ; identity = funext mapId
  ; homomorphism = funext mapHomomorphism2
  ; F-resp-≈ = λ {X} {Y} {f} {g} f≡g → funext λ x →
    begin
      map f x
    ∼⟨ cong-app (cong map f≡g) x ⟩
      map g x
    ∎
  }

-- concatenate two lists
_+L_ : {A : Set} → List A → List A → List A
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

infixr 22 _+L_

-- TASK
-- Prove that +L is associative
+L-assoc : {A : Set} (xs ys zs : List A) → (xs +L ys) +L zs ≡ xs +L (ys +L zs)
+L-assoc [] ys zs =
  begin
    ([] +L ys) +L zs
  ∼⟨⟩
    ys +L zs
  ∼⟨⟩
    [] +L (ys +L zs)
  ∎
+L-assoc (x ,- xs) ys zs =
  begin
    ((x ,- xs) +L ys) +L zs
  ∼⟨⟩
    (x ,- (xs +L ys)) +L zs
  ∼⟨⟩
    x ,- ((xs +L ys) +L zs)
  ∼⟨ cong (x ,-_) (+L-assoc xs ys zs) ⟩
    x ,- (xs +L (ys +L zs))
  ∼⟨⟩
    (x ,- xs) +L (ys +L zs)
  ∎

-- TASK
-- Formulate and prove that [] is a right identity for +L
+L-right-id : {A : Set} (xs : List A) → xs +L [] ≡ xs
+L-right-id [] = refl
+L-right-id (x ,- xs) =
  begin
    (x ,- xs) +L []
  ∼⟨⟩
    x ,- (xs +L [])
  ∼⟨ cong (x ,-_) (+L-right-id xs) ⟩
    x ,- xs
  ∎

-- TASK
-- Implement a function which returns the length of a list as a natural number
length : {A : Set} → List A → ℕ
length [] = zero
length (x ,- xs) = suc (length xs)

mapPreservesLength : {A B : Set} {f : A → B} (xs : List A) → length xs ≡ length (map f xs)
mapPreservesLength {A} {B} {f} [] = refl
mapPreservesLength {A} {B} {f} (x ,- xs) =
    begin
      length (x ,- xs)
    ∼⟨⟩
      suc (length xs)
    ∼⟨ cong suc (mapPreservesLength xs) ⟩
      suc (length (map f xs))
    ∼⟨⟩
      length (map f (x ,- xs))
    ∎

listToNatNatTrans : listFunctor ~> constFunctor ℕ
listToNatNatTrans = record
  { component = λ B → constᶠ ∘ₐ length
  ; commutativity = funext λ xs → cong constᶠ (mapPreservesLength xs)
  }
module listToNatNatTrans = NaturalTransformation listToNatNatTrans

-- +L-is-+ : {A : Set} → listToNatNatTrans.component A {! _+L_ !} ≡ {! _+_ !}

-- TASK
-- Formulate and prove that length is functorial/homomorphic over +L, i.e.
-- the length of the result of +L is the sum of the lengths of its inputs.
+L-length : {A : Set} (xs ys : List A) → length xs +N length ys ≡ length (xs +L ys)
+L-length [] ys = refl
+L-length (x ,- xs) ys =
  begin
    length (x ,- xs) +N length ys
  ∼⟨⟩
    suc (length xs +N length ys)
  ∼⟨ cong suc (+L-length xs ys) ⟩
    suc (length (xs +L ys))
  ∼⟨⟩
    length ((x ,- xs) +L ys)
  ∎

-- TASK
-- Reverse a list by appending to the end of it
reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ,- xs) = reverse xs +L (x ,- [])

-- TASK
-- Prove that reversing twice is the same as not doing anything
-- You'll (most likely) need a lemma which comes as a generalisation of an equality in the recursive case

cons-jumps-left : {A : Set} (xs : List A) (y : A) (ys : List A) → xs +L (y ,- ys) ≡ (xs +L (y ,- [])) +L ys
cons-jumps-left [] y ys = refl
cons-jumps-left (x ,- xs) y ys =
  begin
    (x ,- xs) +L (y ,- ys)
  ∼⟨⟩
    x ,- (xs +L (y ,- ys))
  ∼⟨ cong (x ,-_) (cons-jumps-left xs y ys) ⟩
    x ,- ((xs +L (y ,- [])) +L ys)
  ∼⟨⟩
    ((x ,- xs) +L (y ,- [])) +L ys
  ∎

snoc-jumps-right : {A : Set} (xs : List A) (y : A) → (y ,- []) +L reverse xs ≡ reverse (xs +L (y ,- []))
snoc-jumps-right [] y = refl
snoc-jumps-right (x ,- xs) y =
  begin
    (y ,- []) +L reverse (x ,- xs)
  ∼⟨ cong-app (cong _+L_ (snoc-jumps-right xs y)) (x ,- []) ⟩
    reverse (xs +L (y ,- [])) +L (x ,- [])
  ∼⟨⟩
    reverse ((x ,- xs) +L (y ,- []))
  ∎

reverse-codistributive : {A : Set} (xs ys : List A) → reverse xs +L reverse ys ≡ reverse (ys +L xs)
reverse-codistributive [] [] = refl
reverse-codistributive [] (y ,- ys) =
  begin
    reverse [] +L reverse (y ,- ys)
  ∼⟨⟩
    reverse (y ,- ys)
  ∼⟨⟩
    reverse ys +L (y ,- [])
  ∼⟨ cong-app (cong _+L_ (cong reverse (symmetric (+L-right-id ys)))) (y ,- []) ⟩
    reverse (ys +L []) +L (y ,- [])
  ∼⟨⟩
    reverse ((y ,- ys) +L [])
  ∎
reverse-codistributive (x ,- xs) ys =
  begin
    reverse (x ,- xs) +L reverse ys
  ∼⟨⟩
    (reverse xs +L (x ,- [])) +L reverse ys
  ∼⟨ +L-assoc (reverse xs) (x ,- []) (reverse ys) ⟩
    reverse xs +L (x ,- []) +L reverse ys
  ∼⟨ cong (reverse xs +L_) (snoc-jumps-right ys x) ⟩
    reverse xs +L reverse (ys +L (x ,- []))
  ∼⟨ reverse-codistributive xs (ys +L (x ,- [])) ⟩
    reverse ((ys +L (x ,- [])) +L xs)
  ∼⟨ cong reverse (symmetric (cons-jumps-left ys x xs)) ⟩
    reverse (ys +L (x ,- xs))
  ∎

reverse-reverse-id : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse-id [] = refl
reverse-reverse-id (x ,- xs) =
  begin
     reverse (reverse (x ,- xs))
  ∼⟨⟩
     reverse (reverse xs +L (x ,- []) )
  ∼⟨ symmetric (reverse-codistributive (x ,- []) (reverse xs)) ⟩
     reverse (x ,- []) +L (reverse (reverse xs))
  ∼⟨ cong (reverse (x ,- []) +L_) (reverse-reverse-id xs) ⟩
     reverse (x ,- []) +L xs
  ∼⟨⟩
     (x ,- []) +L xs
  ∼⟨⟩
     x ,- xs
  ∎

-- TASK
-- Implement multiplication using +N
_*N_  : ℕ → ℕ → ℕ
zero *N y = zero
suc x *N y = y +N (x *N y)
infixr 120 _*N_

-- verify that *N behaves normally with a unit test
_ : 5 *N 4 ≡ 20
_ = refl

-- TASK
-- Prove that *N is commutative.
-- Look at your cases and think about what lemmas you needed in +-commut, and try to mirror them here.

*N-right-suc : (n m : ℕ) → n +N (n *N m) ≡ (n *N suc m)
*N-right-suc zero m = refl
*N-right-suc (suc n) m =
  begin
    suc n +N (suc n *N m)
  ∼⟨⟩
    suc (n +N (m +N (n *N m)))
  ∼⟨ cong suc (symmetric (+N-assoc n m (n *N m))) ⟩
    suc ((n +N m) +N (n *N m))
  ∼⟨ cong suc (cong-app (cong _+N_ (+N-symm n m)) (n *N m)) ⟩
    suc ((m +N n) +N (n *N m))
  ∼⟨ cong suc (+N-assoc m n (n *N m)) ⟩
    suc (m +N (n +N (n *N m)))
  ∼⟨ cong suc (cong (m +N_) (*N-right-suc n m)) ⟩
    suc (m +N (n *N suc m))
  ∼⟨⟩
    suc n *N suc m
  ∎
  where
    +N-assoc : (n m k : ℕ) → (n +N m) +N k ≡ n +N (m +N k)
    +N-assoc zero m k = refl
    +N-assoc (suc n) m k =
      ?

    +N-symm : (n m : ℕ) → n +N m ≡ m +N n
    +N-symm = ?

*N-commut : (n m : ℕ) → n *N m ≡ m *N n
*N-commut zero zero = refl
*N-commut zero (suc m) =
  begin
    zero
  ∼⟨ *N-commut zero m ⟩
    m *N zero
  ∎
*N-commut (suc n) m =
  begin
    suc n *N m
  ∼⟨⟩
    m +N (n *N m)
  ∼⟨ cong (m +N_) (*N-commut n m) ⟩
    m +N (m *N n)
  ∼⟨ *N-right-suc m n ⟩
    m *N suc n
  ∎

-- TASK
-- Reverse a list in linear time and constant space by using a helper function
-- The special form of where used below allows us to refer to the definitions inside the
-- where by using a qualified syntax, i.e. we can refer to the inner go with reverseLinear.go
-- Also note that the where bound definition lets us refer to any names bound in the
-- parent function definition, so if we want to refer to A in its signature, we need
-- to explicitly bind the A type argument.
module reverseLinear where
  go : List A → List A → List A
  go [] acc = acc
  go (x ,- xs) acc = go xs (x ,- acc)

reverseLinear : {A : Set} → List A → List A
reverseLinear {A} xs = go xs []
  where
    open reverseLinear using (go)

-- TASK
-- Prove that reversing twice is the same as not doing anything
-- You'll need to formulate a helper lemma for reverseLinear.go
-- Think about what the invariant that reverseLinear.go is trying to maintain is, and how we can extract
-- the correctness property of reverse from it.
reverseLinear-reverseLinear-id : {A : Set} (xs : List A) → reverseLinear (reverseLinear xs) ≡ xs
reverseLinear-reverseLinear-id {A} [] = refl
reverseLinear-reverseLinear-id {A} (x ,- xs) =
  begin
    reverseLinear.go (reverseLinear.go xs (x ,- [])) []
  ∼⟨ cong-app (cong reverseLinear.go (goLem xs (x ,- []))) [] ⟩
    reverseLinear.go (reverse xs +L (x ,- [])) []
  ∼⟨ ? ⟩
    reverseLinear.go (x ,- reverse xs) []
  ∼⟨⟩
    reverseLinear.go (reverse xs) (x ,- [])
  ∼⟨ goLem (reverse xs) (x ,- []) ⟩
    reverse (reverse xs) +L (x ,- [])
  ∼⟨ cong-app (cong _+L_ (reverse-reverse-id xs)) (x ,- []) ⟩
    xs +L (x ,- [])
  ∼⟨ ? ⟩
    x ,- xs
  ∎
  where
    goLem : {A : Set} (xs ys : List A) → reverseLinear.go xs ys ≡ reverse xs +L ys
    goLem = ?

{-
-- TASK
-- Prove that *N distributes over +N on the left
*N-left-distrib-+ : (n m k : ℕ) → n *N (m +N k) ≡ n *N m +N n *N k
*N-left-distrib-+ = ?

-- TASK
-- Prove that *N distributes over +N on the right, by using *N-left-distrib-+ and *N-commut
*N-right-distrib-+ : (n m k : ℕ) → (n +N m) *N k ≡ n *N k +N m *N k
*N-right-distrib-+ n m k = ?

-- TASK
-- Prove *N associative
*N-assoc : (n m k : ℕ) → (n *N m) *N k ≡ n *N (m *N k)
*N-assoc = ?

-- TASK
-- +L and +N are very similar - indeed, if we ignore the elements of the list,
-- they're practically the same function. +L-length which you proved earlier expressed
-- one of the directions of this correspondence.
-- Can you think of some property (with possibly extra definitions) to express the other direction -
-- from +N to +L - of this correspondence?

-- TASK
-- If +N and +L "correspond" with each other, then what would *N correspond with?
-- Implement a function, let's call it _*L_, which you think is *N generalised to lists, and then prove
-- some "functorial"/"homomorphism" properties linking *N and your new *L.

record _*_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _*_ public
infixr 90 _*_

-- TASK
-- Implement list zipping, i.e. combining list elements pointwise, with the longer lists extra elements
-- getting chopped off and dropped.
-- e.g. in Haskell zip [1,2,3,6] [3,4,5] ≡ [(1,3), (2, 4), (3, 5)]
zip : {A B : Set} → List A → List B → List (A * B)
zip = {! !}

-- TASK
-- Does this zip function have some analogue for Nats?
-- Can you prove any properties linking the two?
-- Are there some obvious properties for "the ℕ version of zip" which you can transfer back to zip?
-}
