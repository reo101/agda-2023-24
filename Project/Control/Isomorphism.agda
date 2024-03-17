module Project.Control.Isomorphism where

open import Level using (Level; levelOfTerm; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
-- open module ≡-Reasoning {n} {A} =
--        EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
--          using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; _∘ᶠ_)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Relations using (EquivalenceRelation)

private
  variable
    o₁ ℓ₁ e₁ : Level

record Isomorphism (ℂ : Category {o₁} {ℓ₁} {e₁})
                   {A B : Category.Obj ℂ}
                   (to   : Category._⇒_ ℂ A B)
                   (from : Category._⇒_ ℂ B A)
       : Set (o₁ ⊔ ℓ₁ ⊔ e₁) where
  eta-equality

  private module ℂ = Category ℂ

  field
    isomorphismˡ : ℂ [ ℂ [ from ∘ to ] ≈ ℂ.id ]
    isomorphismʳ : ℂ [ ℂ [ to ∘ from ] ≈ ℂ.id ]
