
module Joro.TwelveLive where

open import Level using (_⊔_) renaming (suc to lsuc)

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
open import Lib.Utils using (id; _∘_)
open import Project.Data.Pair using (Pair; _,_; fst; snd)
open import Project.Data.Maybe using (Maybe; just; nothing)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; fmap; _²) renaming (Id to Idᶠ)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

-- NOTE
-- Let's take a look at the number 3 and a 3 element list
-- suc    (suc    (suc    zero))
-- _,-_ x (_,-_ y (_,-_ z []))
-- Note how these are remarkably similar. It is also true that a lot of the functions on them are also remarkably similar,
-- e.g. +L and +N are almost identical.
--
-- Thanks to the fact that we're allowed to manipulate types as "normal values", it turns out that we can express a very great
-- deal of meta programs directly in Agda, so that we can actually only write "one" single function to implement bot +N and +L.
--
-- We'll take a look at one approach here, although I didn't have the time to flesh all of this out.
-- If you're interested, you should also take a look at indexed containers, polynomial functors, and descriptions (and more?), which
-- are all either alternative approaches or upgrades of Containers.
--
-- A Container is the "description" of something like what we usually imagine a "container" to be.
-- Concretely, a Container describes what the "shape" of something is, and given a shape,
-- what positions it may have items at.
record Container {ℓ₁ ℓ₂} : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    -- We have a type describing all the possible shapes that our container can take.
    -- In order to get some understanding and intuition, it's good to keep in mind the following end goal:
    -- For both natural numbers and lists, this shape will be the natural numbers themselves, so Shape = ℕ,
    -- with the intuition being that we describe a list by "the number of slots it has"
    Shape : Set ℓ₁
    -- Positions are indexed by shapes, because each shape may have different positions
    -- Since our shapes are ℕs indicating how many slots we need to fill, we need to be able
    -- to say that if our shape is n : ℕ, then we have n slots to fill.
    --
    -- This is exactly what Fin does, so we'll use Fin as our Position type for our running example.
    Position : Shape → Set ℓ₂

open Container public

-- NOTE
-- Once we have a container description, we need to be able to turn that description into an
-- "actual" container. So if we assume that we have ListContainer, then [| ListContainer |] : Set → Set
-- will be our notion of a list and correspond to our currently existing List type.
--
-- Do note that this is "just"
-- Shape C >< \shape → Position C shape → A
--
-- However, we choose to avoid _><_, so we can give better names to the fields, as we'll use them a lot.
record [|_|] (C : Container) (A : Set) : Set where
  constructor [|_|>_|]
  field
    -- In order to construct an element of a particular container, we need to pick what the shape will for this element
    -- If we want to represent the initial example here, we'll pick (suc (suc (suc zero))) to be the concrete shape.
    shape : Shape C
    -- and we also need to say, for each position for the chosen shape, what element is in that shape.
    -- In our running example, we've picked out the shape to be (suc (suc (suc zero))), hence
    -- our specialised
    -- elem : Fin 3 → A
    -- will require us to provide three different As for the three different members of Fin 3.
    elem : Position C shape → A

open [|_|] public

-- TASK
-- Implement the ℕ container, as previously discussed.
ℕC : Container
Shape ℕC = ℕ
Position ℕC n = 𝟘

CNat : Set
CNat = [| ℕC |] 𝟙

-- TASK
-- Implement "zero" via CNat
czero : CNat
shape czero = zero
elem czero ()

-- TASK
-- Implmeent the suc function via CNat
csuc : CNat → CNat
csuc [| s |> e |] = [| suc s |> (λ _ → ⟨⟩) |]

-- TASK
-- Implement nat addition for CNat
addCNat : CNat → CNat → CNat
addCNat [| s₁ |> e₁ |] [| s₂ |> e₂ |] = [| s₁ + s₂ |> (λ _ → ⟨⟩) |]
-- addCNat [| zero |> e₁ |] m = {! !}
-- addCNat [| suc s1 |> e1 |] m = addCNat [| s1 |> e1 |] m

-- TASK
-- For a rough smoke test, prove that addCNat behaves the same way as +N

-- TASK
-- Implement the List container, as previously discussed.
ListC : Container
Shape ListC = ℕ
Position ListC n = Fin n

CList : Set → Set
CList = [| ListC |]

-- TASK
-- Implement a generic mapping function that works for any container
cmap : {C : Container} {X Y : Set} → (X → Y) → [| C |] X → [| C |] Y
cmap f [| s |> e |] = [| s |> f ∘ e |]

-- OPTIONAL TASK (untested)
-- Prove that for any Container C, [| C |] induces a functor in the AGDA category.

containerInducesFunctor : Container → HomFunctor HASK
containerInducesFunctor C = record
  { F[_] = [| C |]
  ; fmap = cmap
  ; identity = funext (λ { [| s |> e |] → refl })
  ; homomorphism = refl
  ; F-resp-≈ = λ { refl → refl }
  }

-- TASK
-- Convert an indexing function to a list.
-- It might already be obvious, but this will be useful when working with the positions of a list.
conv : {A : Set} (n : ℕ) → (Fin n → A) → List A
conv zero f = []
conv (suc n) f = f zero ∷ conv n (f ∘ suc)

-- TASK
-- Think about what arguments/callbacks you'll need to provide so that you can convert
-- an arbitrary container to a list.
ctoList :
  {C : Container} {X : Set} →
  (shapeToNat : Shape C → ℕ) →
  ({shape : Shape C} → (Position C shape → X) → Fin (shapeToNat shape) → X) →
  [| C |] X → List X
ctoList shapeToNat f [| s |> e |] = conv (shapeToNat s) (f e)

-- TASK
-- Implement a generic "all" predicate on containers, i.e. All cx P should be inhabited iff
-- all of the elements of of cx satisfy P
CAll : {C : Container} {X : Set} → (cx : [| C |] X) → (P : X → Set) → Set
CAll {C} {X} [| s |> e |] P = 𝟘

{-
-- TASK
-- Implement a generic "any" predicate on containers, i.e. All cx P should be inhabited iff
-- any of the elements of of cx satisfy P
CAny : {C : Container} {X : Set} → (cx : [| C |] X) → (P : X → Set) → Set
CAny = ?

-- TASK
-- Define a "membership relation" over arbitrary containers
CIn : {C : Container} {X : Set} → X → [| C |] X → Set
CIn = ?

-- OPTIONAL TASK (untested)
-- Think about how to define a function, such that given
-- (x : X) → Dec (P x)
-- we can implement
-- ... → Dec (CAll P cx)
-- and
-- ... → Dec (CAny P cx)
--
-- I didn't actually have the time to figure this out, so it's unclear how difficult this is.

-- TASK
-- Implement list append on CLists
appendCList : {X : Set} → CList X → CList X → CList X
appendCList = ?

-- TASK
-- Implement a generic appendContainer which takes suitables HOFs/callbacks, so that you can "append"
-- any two containers.
--
-- Afterwards, reimplement appendCNat and appendCList using the new generic function

-- TASK
-- Implement binary trees via a container description.
--
-- More untested tasks:
-- Try to use ctoList to flatten a binary tree.
-- What can appendContainer do for binary trees?

-- TASK (untested)
-- We saw that containers automatically induce functors in AGDA.
-- It is not too far of a reach to then start thinking about transforming containers themselves, which would correspond to natural transformations.
-- While the container induced convert from [| C |] X to [| C |] Y, can we figure out some data type which represents a transformation/morphism
-- from a container description C1 to a container description C2?
--
record CMorph (C1 C2 : Container) : Set where

-- TASK (untested)
-- You should then, given a CMorph C1 C2, be able to transform one container to another.
<|_|> : {X : Set} {C1 C2 : Container} → CMorph C1 C2 → [| C1 |] X → [| C2 |] X
<|_|> = ?

-- TASK (untested)
-- Can you give container morphisms between the existing example containers you've looked at thus far?

-- TASK (untested)
-- Prove that containers form a category, with the arrows being morphisms between containers.
-}
