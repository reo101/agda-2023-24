module Project.Control.Functor.Algebra where

open import Level using (Level; levelOfTerm; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
-- open module ≡-Reasoning {n} {A} =
--        EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
--          using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; fmap; _∘ᶠ_; _²) renaming (Id to Idᶠ)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)
open import Project.Control.Monad using (Monad)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Relations using (EquivalenceRelation)

-- private
--   variable
--     o ℓ e : Level
--     ℂ : Category {o} {ℓ} {e}
-- 
-- Algebra : (F : HomFunctor ℂ) → (A : Category.Obj ℂ) → Category._⇒_ ℂ (F [ A ]) A
-- Algebra F A = ℂ [ F [ A ] , A ]
--   where
--     module ℂ = Category ℂ
