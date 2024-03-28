module Project.Data.State where

open import Level using (Level; levelOfTerm; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; fmap; _∘ᶠ_; _²) renaming (Id to Idᶠ)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)
open import Project.Control.Monad using (Monad)
open import Project.Control.Adjunction using (Adjunction; _⊣_; monadFromAdjunction)
open import Project.Data.Reader using (Reader; readerFunctor)
open import Project.Data.Pair using (Pair; pairFunctor; _,_)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Relations using (EquivalenceRelation)

open import Lib.Utils using (_∘_; flip)

PairS⊣ReaderS : ∀ {S} → pairFunctor S ⊣ readerFunctor S
PairS⊣ReaderS = record
  { ε = record
    { component = λ A → λ (s , f) → f s
    ; commutativity = λ {X} {Y} {f} → funext λ p →
      begin
        f (Pair.snd p (Pair.fst p))
      ∼⟨ refl ⟩
        f (Pair.snd p (Pair.fst p))
      ∎
    }
  ; η = record
    { component = λ A → flip _,_
    ; commutativity = λ {X} {Y} {f} →
      begin
        (λ x y → y , f x)
      ∼⟨ refl ⟩
        (λ x y → y , f x)
      ∎
    }
  ; identityL = λ {B} → funext λ x →
      begin
       (Pair.fst (Pair.snd x (Pair.fst x)) , (λ x₁ → x₁ , Pair.snd (Pair.snd x (Pair.fst x))))
      ∼⟨ ? ⟩
        x
      ∎
  ; identityR = λ {A} → funext λ x →
      begin
        (λ x₁ → x₁ , (λ x₂ → Pair.snd (x x₂) (Pair.fst (x x₂))))
      ∼⟨ ? ⟩
        x
      ∎
  }

State : ∀ {S} → ∀ (A) → ? -- (Reader S ∘ Pair S) A
State {S} = PairS⊣ReaderS.η.component
  where
    module PairS⊣ReaderS = Adjunction (PairS⊣ReaderS {S})

stateMonad : ∀ {S} → Monad HASK
stateMonad {S} = monadFromAdjunction (PairS⊣ReaderS {S})
