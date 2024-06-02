{-# OPTIONS --type-in-type #-}

module Joro.ElevenLive where

open import Lib.Zero using (𝟘; zero-elim; ¬_)
open import Lib.One using (𝟙; ⟨⟩)
open import Lib.Two using (𝟚; tt; ff)
open import Lib.Nat using (ℕ; zero; suc; _+_; ozero; osuc; _≤_; ≤-refl; ≤-suc; ≤-trans; +-right-suc) renaming (_<_ to Lt)
open import Lib.Fin using (Fin; zero; suc; natToFin; finToNat)
open import Lib.Number using (Number; fromNat; Numℕ; NumFin)
-- open import Lib.Sum using (_+_; inl; inr)
open import Lib.Sigma using (Σ; _*_) renaming (_,_ to _,σ_)
open import Lib.Decidable using (Dec; no; yes)
open import Lib.List using (List; []; _∷_; _+L_; length; +L-right-id; +L-assoc)
open import Lib.Vec using (Vec; HetVec; []; _∷_; congₙ)
open import Lib.Utils using (id)
open import Project.Data.Pair using (Pair; _,_; fst; snd)
open import Project.Data.Maybe using (Maybe; just; nothing)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)



-- TODO:
-- discuss levels briefly
-- example: list of types
-- example: record containing Sets
--
-- TODO: {-# OPTIONS --type-in-type #-}
--
-- TODO: postulate

-- "тип"
-- data ℕ : Set where
-- data List (A : Set) : Set where
-- data List {l : Level} (A : Set l) : Set (l + 1) where
--
-- List : ?????
-- Set : ?????

-- Set : Set

-- Set0 : Set1
-- Set1 : Set2
-- Set2 : ...
-- Set_n : Set_(n+1)

-- Set : Set

--record Foo : Set where
--  field
--    bar : Set


-- TODO: categories as an abstraction for compositions
-- TODO: reminder on copatterns, going to be useful again
-- TODO: AGDA as an example
-- TODO: THREE as an example

-- TODO: monoids in general
-- TODO: monoids as single object categories
-- "all of the info is in the arrows"
-- TODO: + as example

-- TODO: preorders
-- "all of the info is in the objects"/"it doesn't matter how you get from object A to object B"
-- TODO: _≤_ as example

-- TODO: functors as an abstraction for homomorphisms
-- TODO: Maybe as an example

-- TODO: extensionality
-- example: addℕ defined on its two args
-- example: linear search vs binary search

record Category : Set where
  field
    Obj : Set
    Arr : (x : Obj) → (y : Obj) → Set
    idArr : {x : Obj} → Arr x x
    comp :
      {x y z : Obj} →
      (f : Arr x y) →
      (g : Arr y z) →
      Arr x z
    idArr-comp :
      {x y : Obj}
      (f : Arr x y) →
      comp (idArr {x}) f ≡ f
    comp-idArr :
      {x y : Obj}
      (f : Arr x y) →
      comp f (idArr {y}) ≡ f
    assoc :
      {x y z w : Obj}
      (f : Arr x y) (g : Arr y z) (h : Arr z w) →
      comp (comp f g) h ≡ comp f (comp g h)

open Category public

-- id : {A : Set} → A → A
-- id x = x

-- NOTE
-- Function composition
_>>_ : {S R T : Set} → (S → R) → (R → T) → S → T
_>>_ f g x = g (f x)

-- C-c C-c
AGDA : Category
Obj AGDA = Set
Arr AGDA A B = A → B
idArr AGDA = id
comp AGDA = _>>_
idArr-comp AGDA f = refl
-- comp idArr f
-- _>>_ idArr f
-- _>>_ id f
-- _>>_ (\x → x) f
-- (\y → _>>_ (\x → x) f y)
-- (\y → f ((\x → x) y))
-- (\y → f y)
comp-idArr AGDA f = refl
assoc AGDA f g h = refl
-- comp (comp f g) h ≡ comp f (comp g h)
-- (f >> g) >> h ≡ f >> (g >> h)

-- * -→ *
--  \    |
--   \   |
--    \  |
--     \ |
--      \|
--       v
--       *
module Three where
  data Three : Set where
    -- zero : Three
    -- one : Three
    -- two : Three
    zero one two : Three

  data Arrow : Three → Three → Set where
    idArrThree : {x : Three} → Arrow x x
    zero-one : Arrow zero one
    one-two : Arrow one two
    zero-two : Arrow zero two


  THREE : Category
  Obj THREE = Three
  Arr THREE = Arrow
  idArr THREE = idArrThree
  comp THREE idArrThree g = g
  comp THREE f idArrThree = f
  comp THREE zero-one one-two = zero-two
  idArr-comp THREE f = refl
  comp-idArr THREE idArrThree = refl
  comp-idArr THREE zero-one = refl
  comp-idArr THREE one-two = refl
  comp-idArr THREE zero-two = refl
  assoc THREE idArrThree idArrThree idArrThree = refl
  assoc THREE idArrThree idArrThree zero-one = refl
  assoc THREE idArrThree idArrThree one-two = refl
  assoc THREE idArrThree idArrThree zero-two = refl
  assoc THREE idArrThree zero-one idArrThree = refl
  assoc THREE idArrThree zero-one one-two = refl
  assoc THREE idArrThree one-two idArrThree = refl
  assoc THREE idArrThree zero-two idArrThree = refl
  assoc THREE zero-one idArrThree idArrThree = refl
  assoc THREE zero-one idArrThree one-two = refl
  assoc THREE zero-one one-two idArrThree = refl
  assoc THREE one-two idArrThree idArrThree = refl
  assoc THREE zero-two idArrThree idArrThree = refl

-- NOTE
-- "All of the info is in the objects", since there's at most one arrow between any two objects.
-- Effectively this means that with preorders we don't care how exactly we get from an arrow A to B,
-- just that there is one
record Preorder : Set where
  field
    cat : Category
    one-arrow :
      {x y : Obj cat} →
      (f g : Arr cat x y) →
      f ≡ g


≤-unique : {n m : ℕ} (p q : n ≤ m) → p ≡ q
≤-unique ozero ozero = refl
≤-unique (osuc p) (osuc q) = cong osuc (≤-unique p q)

skapana-agda-iskam-lean : ∀ {x y} → {f : x ≤ y} → ≤-trans f (≤-refl y) ≡ f
skapana-agda-iskam-lean {f = ozero} = refl
skapana-agda-iskam-lean {f = osuc f} = cong osuc skapana-agda-iskam-lean

skapana-agda-iskam-lean′ : ∀ {x y} → {f : x ≤ y} → ≤-trans (≤-refl x) f ≡ f
skapana-agda-iskam-lean′ {f = ozero} = refl
skapana-agda-iskam-lean′ {f = osuc f} = cong osuc skapana-agda-iskam-lean′

-- TASK
≤-Cat : Category
Obj ≤-Cat = ℕ
Arr ≤-Cat = _≤_
idArr ≤-Cat {n} = ≤-refl n
comp ≤-Cat = ≤-trans
-- idArr-comp ≤-Cat ozero = refl
-- idArr-comp ≤-Cat (osuc f) = cong osuc (idArr-comp ≤-Cat f)
idArr-comp ≤-Cat f = skapana-agda-iskam-lean′ {f = f}
comp-idArr ≤-Cat f = skapana-agda-iskam-lean {f = f}
assoc ≤-Cat = {! ≤-unique ? ? !}

-- TASK
≤-Preorder : Preorder
≤-Preorder = ?

-- NOTE
-- "All of the info is in the arrows", since we only have one object.
-- Effectively this means that we only care about the arrows, and the case is usually that we have some operations as arrows.
record Monoid : Set where
  field
    cat : Category
    Obj-is-One : Obj cat ≡ 𝟙

-- TASK
ℕ+-Cat : Category
Obj ℕ+-Cat = 𝟙
Arr ℕ+-Cat _ _ = ℕ
idArr ℕ+-Cat = zero
comp ℕ+-Cat = _+_
idArr-comp ℕ+-Cat = {! !}
comp-idArr ℕ+-Cat = {! !}
assoc ℕ+-Cat = {! !}

ℕ+-Monoid : Monoid
ℕ+-Monoid = ?

-- f : G → H
-- f (eps_G) ≡ eps_H
-- f (x <G> y) ≡ f (x) <H> f (y)
-- F ((f >> g)) ≡ F f >> F g

-- Functor
record _=>_ (C D : Category) : Set where
  field
    F-Obj : Obj C → Obj D
    F-map :
      {x y : Obj C} →
      (f : Arr C x y) →
      Arr D (F-Obj x) (F-Obj y)

    F-map-id :
      (x : Obj C) →
      F-map (idArr C {x}) ≡ idArr D {F-Obj x}

    F-map-comp :
      {x y z : Obj C}
      (f : Arr C x y) (g : Arr C y z) →
      F-map (comp C f g) ≡ comp D (F-map f) (F-map g)

open _=>_ public

-- data Maybe (A : Set) : Set where
--   just : A → Maybe A
--   nothing : Maybe A

-- има аксиома ext
postulate
  ext :
    {A B : Set} {f g : A → B} →
    ((x : A) → f x ≡ g x) →
    f ≡ g

-- linear search
-- binary search

-- TASK
-- A category with one object
-- *
ONE : Category
Obj ONE = 𝟙
Arr ONE _ _ = 𝟙
idArr ONE = ⟨⟩
comp ONE = λ f g → ⟨⟩
idArr-comp ONE ⟨⟩ = refl
comp-idArr ONE ⟨⟩ = refl
assoc ONE ⟨⟩ ⟨⟩ ⟨⟩ = refl

-- TASK
-- A category with two objects, with an arrow between them
-- * -→ *
module TwoCat where
  data ArrTwo : 𝟚 → 𝟚 → Set where
    idArrTwo : {t : 𝟚} → ArrTwo t t
    arrArrTwo : ArrTwo ff tt

  TWO : Category
  Obj TWO = 𝟚
  Arr TWO = ArrTwo
  idArr TWO = idArrTwo
  comp TWO idArrTwo idArrTwo = idArrTwo
  comp TWO idArrTwo arrArrTwo = arrArrTwo
  comp TWO arrArrTwo idArrTwo = arrArrTwo
  idArr-comp TWO idArrTwo = refl
  idArr-comp TWO arrArrTwo = refl
  comp-idArr TWO idArrTwo = refl
  comp-idArr TWO arrArrTwo = refl
  assoc TWO idArrTwo idArrTwo idArrTwo = refl
  assoc TWO idArrTwo idArrTwo arrArrTwo = refl
  assoc TWO idArrTwo arrArrTwo idArrTwo = refl
  assoc TWO arrArrTwo idArrTwo idArrTwo = refl

-- TASK
-- Similarly to ℕ+-Cat, +L induces a category which is also a monoid.
-- The objects will be One, since it's a monoid, and the arrows will be given by the
-- list append operation (_+L_).
List-+L-Cat : Set → Category
Obj (List-+L-Cat X) = 𝟙
Arr (List-+L-Cat X) ⟨⟩ ⟨⟩ = List X
idArr (List-+L-Cat X) {x} = []
comp (List-+L-Cat X) f g = f +L g
idArr-comp (List-+L-Cat X) f = refl
comp-idArr (List-+L-Cat X) f = +L-right-id f
assoc (List-+L-Cat X) f g h = +L-assoc f g h

-- TASK
List-+L-Monoid : Set → Monoid
Monoid.cat (List-+L-Monoid X) = List-+L-Cat X
Monoid.Obj-is-One (List-+L-Monoid X) = refl

-- TASK
-- A Discrete category is one in which the only arrows are the identity arrows
-- An example of such a category is the one formed with an arbitrary type, and _≡_ as arrows
-- Implement the discrete category where the objects are elements of the type X, and
-- the arrows are the equalities between those elements.
module DiscreteEq (X : Set) where
  Discrete≡ : Category
  Obj Discrete≡ = X
  Arr Discrete≡ = _≡_
  idArr Discrete≡ = refl
  comp Discrete≡ refl refl = refl
  idArr-comp Discrete≡ refl = refl
  comp-idArr Discrete≡ refl = refl
  assoc Discrete≡ refl refl refl = refl

-- TASK
-- We can make a category with whatever arrows we like if our objects are Zero.
module EmptyCat (Arrows : Set) where
  EMPTY : Category
  Obj EMPTY = 𝟘
  Arr EMPTY ()
  idArr EMPTY {()}
  comp EMPTY {()}
  idArr-comp EMPTY {()}
  comp-idArr EMPTY {()}
  assoc EMPTY {()}

-- TASK
-- We can always flip the directions of arrows in a category to form the "opposite" category.
-- This actually turns out to be a very useful concept in general.
Op : Category → Category
Obj (Op C) = Obj C
Arr (Op C) = λ x y → Arr C y x
idArr (Op C) = idArr C
comp (Op C) = λ f g → comp C g f
idArr-comp (Op C) = comp-idArr C
comp-idArr (Op C) = idArr-comp C
assoc (Op C) f g h = sym (assoc C h g f)

-- TASK
-- Given two categories, we can form their product, by having objects which are tuples of objects
-- of our original categories, and lifting everything from our original categories pointwise for those tuples.
-- _*_ is your friend.
Product : Category → Category → Category
Obj (Product C D) =
  Pair (Obj C) (Obj D)
Arr (Product C D) (x₁ , x₂) (y₁ , y₂) =
  Pair (Arr C x₁ y₁) (Arr D x₂ y₂)
idArr (Product C D) {x₁ , x₂} =
  idArr C , idArr D
comp (Product C D) {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} (f₁ , f₂) (g₁ , g₂) =
  comp C f₁ g₁ , comp D f₂ g₂
idArr-comp (Product C D) {x₁ , y₁} {x₂ , y₂} (f₁ , f₂) =
  congₙ _,_ ((comp C (idArr C) f₁ , f₁) ∷ (comp D (idArr D) f₂ , f₂) ∷ [])
            (idArr-comp C f₁            ∷ idArr-comp D f₂            ∷ [])
comp-idArr (Product C D) {x₁ , y₁} {x₂ , y₂} (f₁ , f₂) =
  congₙ _,_ ((comp C f₁ (idArr C) , f₁) ∷ (comp D f₂ (idArr D) , f₂) ∷ [])
            (comp-idArr C f₁            ∷ comp-idArr D f₂            ∷ [])
assoc (Product C D) {x₁ , x₂} {y₁ , y₂} {z₁ , z₂} {w₁ , w₂} (f₁ , f₂) (g₁ , g₂) (h₁ , h₂) =
  congₙ _,_ ((comp C (comp C f₁ g₁) h₁ , comp C f₁ (comp C g₁ h₁)) ∷
             (comp D (comp D f₂ g₂) h₂ , comp D f₂ (comp D g₂ h₂)) ∷
             [])
            (assoc C f₁ g₁ h₁ ∷
             assoc D f₂ g₂ h₂ ∷
             [])

-- TASK
-- "Doing nothing" is a functor, i.e. we don't change the objects and we don't change the arrows.
ID : (C : Category) → C => C
F-Obj (ID C) = id
F-map (ID C) f = f
F-map-id (ID C) x = refl
F-map-comp (ID C) f g = refl

fmapMaybe :
  {A B : Set} →
  (A → B) →
  Maybe A →
  Maybe B
fmapMaybe f (just x) = just (f x)
fmapMaybe f nothing = nothing

fmapMaybe-id :
  {A : Set}
  (x : Maybe A) →
  fmapMaybe id x ≡ x
fmapMaybe-id (just x) = refl
fmapMaybe-id nothing = refl

-- TASK
MAYBE : AGDA => AGDA
F-Obj MAYBE A = Maybe A
F-map MAYBE = fmapMaybe
F-map-id MAYBE a =
  ext fmapMaybe-id
F-map-comp MAYBE f g = funext λ
  { nothing → refl
  ; (just x) → refl
  }

-- TASK
map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- TASK
-- Mapping with the iden
map-id : {A : Set} (xs : List A) → map id xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

-- TASK
-- Mapping with a composition of functions is the same as mapping with
-- one function, and then mapping with the other function.
map-compose :
  {A B C : Set} (f : A → B) (g : B → C) (xs : List A) →
  map (f >> g) xs ≡ map g (map f xs)
map-compose f g [] = refl
map-compose f g (x ∷ xs) = cong (g (f x) ∷_) (map-compose f g xs)

-- TASK
-- The List type constructor is a functor, in the same way that Maybe is a functor.
LIST : AGDA => AGDA
F-Obj LIST A = List A
F-map LIST f xs = map f xs
F-map-id LIST A = funext map-id
F-map-comp LIST f g = funext (map-compose f g)

-- TASK
-- Addition with the constant k forms a functor over the preorder ℕ category
ADD : ℕ → ≤-Cat => ≤-Cat
F-Obj (ADD k) x = k + x
F-map (ADD zero) f = f
F-map (ADD (suc k)) f = osuc (F-map (ADD k) f)
F-map-id (ADD zero) x = refl
F-map-id (ADD (suc k)) x = cong osuc (F-map-id (ADD k) x)
F-map-comp (ADD zero) f g = refl
F-map-comp (ADD (suc k)) f g = cong osuc (F-map-comp (ADD k) f g)

-- TASK
-- Mapping with a function (f : X → Y) over a list induces a functor between the monoid
-- categories of lists over X and Y respectively.
LIST+L : {X Y : Set} (f : X → Y) → List-+L-Cat X => List-+L-Cat Y
F-Obj (LIST+L f) _ = ⟨⟩
F-map (LIST+L f) [] = []
F-map (LIST+L f) (x ∷ xs) = f x ∷ F-map (LIST+L f) xs
F-map-id (LIST+L f) x = refl
F-map-comp (LIST+L f) [] ys = refl
F-map-comp (LIST+L f) (x ∷ xs) ys = cong (f x ∷_) (F-map-comp (LIST+L f) xs ys)

-- TASK
-- Define the "is prefix of" relation between lists
data _≤L_ {A : Set} : List A → List A → Set where
  ≤-[] : {ys : List A} → [] ≤L ys
  ≤-∷ : {x : A} {xs ys : List A} → xs ≤L ys → x ∷ xs ≤L x ∷ ys

infix 15 _≤L_
 
module ≤L-Cats {A : Set} where
  -- TASK
  -- Prove that lists of A equipped with _≤L_ form a category
  ≤L-Cat : Category
  Obj ≤L-Cat = List A
  Arr ≤L-Cat = _≤L_
  idArr ≤L-Cat {[]} = ≤-[]
  idArr ≤L-Cat {x ∷ xs} = ≤-∷ {x = x} {xs = xs} {ys = xs} (idArr ≤L-Cat)
  comp ≤L-Cat ≤-[] g = ≤-[]
  comp ≤L-Cat (≤-∷ f) (≤-∷ g) = ≤-∷ (comp ≤L-Cat f g)
  idArr-comp ≤L-Cat ≤-[] = refl
  idArr-comp ≤L-Cat (≤-∷ f) = cong ≤-∷ (idArr-comp ≤L-Cat f)
  comp-idArr ≤L-Cat ≤-[] = refl
  comp-idArr ≤L-Cat (≤-∷ f) = cong ≤-∷ (comp-idArr ≤L-Cat f)
  assoc ≤L-Cat ≤-[] ≤-[] ≤-[] = refl
  assoc ≤L-Cat ≤-[] ≤-[] (≤-∷ h) = refl
  assoc ≤L-Cat ≤-[] (≤-∷ g) (≤-∷ h) = refl
  assoc ≤L-Cat (≤-∷ f) (≤-∷ g) (≤-∷ h) = cong ≤-∷ (assoc ≤L-Cat f g h)

  -- TASK
  -- Prove that that category is a preorder
  ≤L-Preorder : Preorder
  Preorder.cat ≤L-Preorder = ≤L-Cat
  Preorder.one-arrow ≤L-Preorder ≤-[] ≤-[] = refl
  Preorder.one-arrow ≤L-Preorder (≤-∷ f) (≤-∷ g) = cong ≤-∷ (Preorder.one-arrow ≤L-Preorder f g)

  -- TASK
  -- We can form a functor from list prefixes to _≤_.
  -- Implement it.
  Drop-Elems : ≤L-Cat => ≤-Cat
  F-Obj Drop-Elems = length
  F-map Drop-Elems ≤-[] = ozero
  F-map Drop-Elems (≤-∷ f) = osuc (F-map Drop-Elems f)
  F-map-id Drop-Elems [] = refl
  F-map-id Drop-Elems (x ∷ xs) = cong osuc (F-map-id Drop-Elems xs)
  F-map-comp Drop-Elems ≤-[] g = refl
  F-map-comp Drop-Elems (≤-∷ f) (≤-∷ g) = cong osuc (F-map-comp Drop-Elems f g)

-- TASK
-- Implement the function which takes a prefix of n elements from a Vector of size m,
-- by using the proof that n ≤ m to allow us to do so
-- We've already implement this previously, so feel free to copy it if you'd like
vTake : {A : Set} {n m : ℕ} → n ≤ m → Vec A m → Vec A n
vTake ozero xs = []
vTake (osuc f) (x ∷ xs) = x ∷ vTake f xs

-- TASK
-- vTake gives rise to a functor, sending _≤_ functions over Vec A
-- If we look at vTakes signature, we'll notice that n ≤ m is transformed into (Vec A m → Vec A n) -
-- note how the places of n and m are swapped.
-- As a consequence, we need to use the opposite cateogry of ≤-Cat here, to make things line up.
{-# TERMINATING #-}
VTAKE : Set → Op ≤-Cat => AGDA
F-Obj (VTAKE X) n = Vec X n
F-map (VTAKE X) {m} {n} f xs = vTake f xs
F-map-id (VTAKE X) zero = funext λ { [] → refl }
F-map-id (VTAKE X) (suc n) = funext λ { (x ∷ xs) → cong (x ∷_) (cong-app (F-map-id (VTAKE X) n) xs) }
F-map-comp (VTAKE X) ozero ozero = funext λ { [] → refl
                                            ; (x ∷ xs) → refl }
F-map-comp (VTAKE X) (osuc f) ozero = funext λ { (x ∷ xs) → refl }
F-map-comp (VTAKE X) (osuc f) (osuc g) = funext λ { (x ∷ xs) → cong (x ∷_) (cong-app (F-map-comp (VTAKE X) f g) xs) }

module FreeCat (X : Set) (R : X → X → Set) where
  -- TASK
  -- Given a type X and a binary relation R over X, we can form a "free category" based on X and R in the usual sense of "free algebraic structure".
  -- That is, we will force all the properties required of a category to hold synthetically, by introducing a new relation Free R : X → X → Set,
  -- such that X and Free R form a category.
  --
  -- Essentially, this means that we want to add some additional properties to R to get Free R, so that we can then prove our Category laws
  --
  -- Implement the datatype Free which adds those properties to R. It might be helpful to first try implementing the FREE
  -- category, to figure out what exactly you need.
  data Free : X → X → Set where
    free-id : {x : X} → Free x x
    free-comp : {x y z : X} → Free x y → Free y z → Free x z
    free-real : {x y : X} → R x y → Free x y

  -- TASK
  -- Since Free will form the arrows for our category, we will of course also need a way to compose Frees
  compFree : {x y z : X} → Free x y → Free y z → Free x z
  compFree = free-comp

  -- TASK
  -- Implement the free category over X and R by using Free and compFree
  FREE : Category
  Obj FREE = X
  Arr FREE = Free
  idArr FREE = free-id
  comp FREE = free-comp
  idArr-comp FREE free-id = {! !}
  idArr-comp FREE (free-comp f₁ f₂) = {! !}
  idArr-comp FREE (free-real r) = {! !}
  comp-idArr FREE = {! !}
  assoc FREE = {! !}

module Finite where
  -- TASK
  -- We've seen a few finite categories - ZERO, TWO, THREE
  -- We can take advantage of Fin n to define a generalised finite category, mimicking THREE.
  -- If we want a category "of size n", we'll take Fin n to be the objects.
  --
  -- The arrows will roughly be defined as
  -- n ~> m iff n ≤ m
  --
  -- Think about how to define all of these and implement the FINITE category.

  FINITE : ℕ → Category
  Obj (FINITE n) = Fin n
  Arr (FINITE zero) () y
  Arr (FINITE (suc n)) zero y = 𝟙
  Arr (FINITE (suc n)) (suc x) zero = 𝟘
  Arr (FINITE (suc n)) (suc x) (suc y) = Arr (FINITE n) x y
  idArr (FINITE (suc n)) {zero} = ⟨⟩
  idArr (FINITE (suc n)) {suc x} = idArr (FINITE n)
  comp (FINITE (suc n)) {zero} {zero} {zero} f g = ⟨⟩
  comp (FINITE (suc n)) {zero} {zero} {suc z} f g = ⟨⟩
  comp (FINITE (suc n)) {zero} {suc y} {suc z} f g = ⟨⟩
  comp (FINITE (suc n)) {suc x} {suc y} {suc z} f g = comp (FINITE n) {x} {y} {z} f g
  idArr-comp (FINITE (suc n)) {zero} {zero} ⟨⟩ = refl
  idArr-comp (FINITE (suc n)) {zero} {suc y} ⟨⟩ = refl
  idArr-comp (FINITE (suc n)) {suc x} {suc y} f = idArr-comp (FINITE n) {x} {y} f
  comp-idArr (FINITE (suc n)) {zero} {zero} ⟨⟩ = refl
  comp-idArr (FINITE (suc n)) {zero} {suc y} ⟨⟩ = refl
  comp-idArr (FINITE (suc n)) {suc x} {suc y} f = comp-idArr (FINITE n) {x} {y} f
  assoc (FINITE (suc n)) {zero} {zero} {zero} {zero} f g h = refl
  assoc (FINITE (suc n)) {zero} {zero} {zero} {suc w} f g h = refl
  assoc (FINITE (suc n)) {zero} {zero} {suc z} {suc w} f g h = refl
  assoc (FINITE (suc n)) {zero} {suc y} {suc z} {suc w} f g h = refl
  assoc (FINITE (suc n)) {suc x} {suc y} {suc z} {suc w} f g h = assoc (FINITE n) {x} {y} {z} {w} f g h

  FINITE′ : ℕ → Category
  Obj (FINITE′ n) = Fin n
  Arr (FINITE′ n) x y = finToNat x ≤ finToNat y
  idArr (FINITE′ (suc n)) {zero} = ozero
  idArr (FINITE′ (suc n)) {suc x} = osuc (idArr (FINITE′ n) {x})
  comp (FINITE′ (suc n)) {zero} {zero} {zero} ozero ozero = ozero
  comp (FINITE′ (suc n)) {zero} {zero} {suc z} ozero ozero = ozero
  comp (FINITE′ (suc n)) {zero} {suc y} {suc z} ozero (osuc g) = ozero
  comp (FINITE′ (suc n)) {suc x} {suc y} {suc z} (osuc f) (osuc g) = osuc (comp (FINITE′ n) {x} {y} {z} f g)
  idArr-comp (FINITE′ (suc n)) {zero} {zero} ozero = refl
  idArr-comp (FINITE′ (suc n)) {zero} {suc y} ozero = refl
  idArr-comp (FINITE′ (suc n)) {suc x} {suc y} (osuc f) = cong osuc (idArr-comp (FINITE′ n) {x} {y} f)
  comp-idArr (FINITE′ (suc n)) {zero} {zero} ozero = refl
  comp-idArr (FINITE′ (suc n)) {zero} {suc y} ozero = refl
  comp-idArr (FINITE′ (suc n)) {suc x} {suc y} (osuc f) = cong osuc (comp-idArr (FINITE′ n) {x} {y} f)
  assoc (FINITE′ (suc n)) {zero} {zero} {zero} {zero} ozero ozero ozero = refl
  assoc (FINITE′ (suc n)) {zero} {zero} {zero} {suc w} ozero ozero ozero = refl
  assoc (FINITE′ (suc n)) {zero} {zero} {suc z} {suc w} ozero ozero (osuc h) = refl
  assoc (FINITE′ (suc n)) {zero} {suc y} {suc z} {suc w} ozero (osuc g) (osuc h) = refl
  assoc (FINITE′ (suc n)) {suc x} {suc y} {suc z} {suc w} (osuc f) (osuc g) (osuc h) = cong osuc (assoc (FINITE′ n) {x} {y} {z} {w} f g h)
