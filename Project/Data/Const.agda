module Project.Data.Const where

open import Level using (Level; zero; suc; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
module HASK = Category HASK
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_])
open import Project.Control.Monad using (Monad)
open import Project.Postulates using (funext)

record Const (A B : Set) : Set where
  eta-equality
  constructor constᶠ
  field
    elem : A
open Const

constFunctor : (A : Set) → HomFunctor HASK
constFunctor A = record
  { F[_] = Const A
  ; fmap = λ {B₁} {B₂} f → λ (constᶠ a) → (constᶠ a)
  ; identity =
      funext λ (constᶠ a) → refl
  ; homomorphism =
      funext λ (constᶠ a) → refl
  ; F-resp-≈ = λ {X} {Y} {f} {g} C[f≈g] →
      funext λ (constᶠ a) → refl
  }
