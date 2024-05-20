module Project.Data.Free where

open import Level using (Level; zero; suc; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
module HASK = Category HASK
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; _∘ᶠ_) renaming (Id to Idᶠ)
open import Project.Control.Monad using (Monad)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)
open import Project.Data.Reader using (Reader; readerFunctor)
open import Project.Data.Pair using (Pair; pairFunctor; _,_)
open import Project.Postulates using (funext)
open import Lib.One using (𝟙; ⟨⟩)
open import Lib.Utils using (_∘_; id; flip; const)

private
  variable
    A B : Set

-- NOTE: Functors are not Stricty Positive Types (Indexed Containers)
--       <https://www.sciencedirect.com/science/article/pii/S0304397505003373>
{-# NO_POSITIVITY_CHECK #-}
data Free (F : HomFunctor HASK) (A : Set) : Set where
  pure : A → Free F A
  impure : F [ Free F A ] → Free F A

module FreeTakiva (F : HomFunctor HASK) where
  module F = Functor F

  {-# TERMINATING #-}
  freeFmap : (A → B) → Free F A → Free F B
  freeFmap f (pure x) = pure (f x)
  freeFmap f (impure x) = impure ((F [fmap freeFmap f ]) x)

  {-# TERMINATING #-}
  freeIdentity : freeFmap {A = A} id ≡ id
  freeIdentity = funext λ
    { (pure x) → refl
    ; (impure x) →
      begin
        impure ((F [fmap freeFmap id ]) x)
      ∼⟨ cong impure (cong-app (F.F-resp-≈ freeIdentity) x) ⟩
        impure ((F [fmap id ]) x)
      ∼⟨ cong impure (cong-app F.identity x) ⟩
        impure (id x)
      ∼⟨⟩
        impure x
      ∎
    }

  {-# TERMINATING #-}
  freeHomomorphism : {X Y Z : Set} {f : X → Y} {g : Y → Z} → freeFmap (g ∘ f) ≡ (freeFmap g ∘ freeFmap f)
  freeHomomorphism {X} {Y} {Z} {f} {g} = funext λ
    { (pure x) → refl
    ; (impure x) →
      begin
        impure ((F [fmap (freeFmap (g ∘ f)) ]) x)
      ∼⟨ cong impure (cong-app (cong (F [fmap_]) freeHomomorphism) x) ⟩
        impure ((F [fmap (freeFmap g ∘ freeFmap f)]) x)
      ∼⟨ cong impure (cong-app F.homomorphism x) ⟩
        impure (((F [fmap freeFmap g ]) ∘ (F [fmap freeFmap f ])) x)
      ∎
    }

  freeF-resp-≈ : {X Y : Set} {f g : X → Y} → f ≡ g → freeFmap f ≡ freeFmap g
  freeF-resp-≈ {X} {Y} {f} {g} f≈g = funext λ
    { (pure x) →
      begin
        pure (f x)
      ∼⟨ cong pure (cong-app f≈g x) ⟩
        pure (g x)
      ∎
    ; (impure x) →
      begin
        impure ((F [fmap freeFmap f ]) x)
      ∼⟨ cong impure (cong-app (cong (F [fmap_]) (cong freeFmap f≈g)) x) ⟩
        impure ((F [fmap freeFmap g ]) x)
      ∎
    }

  freeFunctor : HomFunctor HASK
  freeFunctor = record
    { F[_] = Free F
    ; fmap = freeFmap
    ; identity = freeIdentity
    ; homomorphism = freeHomomorphism
    ; F-resp-≈ = freeF-resp-≈
    }

  module FreeF = Functor freeFunctor

  η : A → Free F A
  η = pure

  {-# TERMINATING #-}
  μ : Free F (Free F A) → Free F A
  μ (pure x) = x
  μ (impure x) = impure ((F [fmap μ ]) x)

  freeMonad : Monad HASK
  freeMonad = record
    { F = freeFunctor
    ; η = record
      { component = λ { A → η {A} }
      ; commutativity = {! !}
      }
    ; μ = record
      { component = λ { A → μ {A} }
      ; commutativity = {! !}
      }
    ; μμ-associative = {! !}
    ; μη-associative = {! !}
    ; μη-identity = {! !}
    }

open FreeTakiva public using (freeFunctor; freeMonad)

module _ where
  private
    variable
      S : Set

  StateF : (S : Set) → HomFunctor HASK
  StateF S = readerFunctor S ∘ᶠ pairFunctor S
  -- StateF S = record
  --   { F[_] = λ { A → (S → Pair S A) }
  --   ; fmap = {! !}
  --   ; identity = {! !}
  --   ; homomorphism = {! !}
  --   ; F-resp-≈ = {! !} }

  State : Set → Set → Set
  State = Free ∘ StateF

  _>>=_ : {{m : Monad HASK}} →
          let open Monad m using (F)
          in
          F [ A ] →
          (A → F [ B ]) →
          F [ B ]
  _>>=_ {B = B} {{m}} mx f = μ.component B ((F [fmap f ]) mx)
    where
      open Monad m using (F; μ)

  _>>_ : {{m : Monad HASK}} →
         let open Monad m using (F)
         in
         F [ A ] →
         F [ B ] →
         F [ B ]
  _>>_ {B = B} {{m}} mx my = μ.component B ((F [fmap const my ]) mx)
    where
      open Monad m using (F; μ)

  open import Lib.Nat using (ℕ; _+_)

  get : State S S
  get = impure λ { s → s , pure s }

  set : S → State S 𝟙
  set s = impure λ { s′ → s , pure ⟨⟩ }

  kek : State ℕ ℕ
  kek = do
    a ← get
    set (a + 1)
    pure (a + 3)
    where
      instance
        _ : Monad HASK
        _ = freeMonad (StateF ℕ)

  runState : State S A → S → Pair S A
  runState (pure x) s = s , x
  runState (impure f) s =
    let s′ , b = f s
     in runState b s′

  _ : runState kek 5 ≡ 6 , 8
  _ = refl
