module Project.Control.Categories.Cat where

open import Level using (Level; levelOfTerm; suc; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
-- open module ≡-Reasoning {n} {A} =
--        EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
--          using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; fmap; _∘ᶠ_; _²) renaming (Id to Idᶠ)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)
open import Project.Control.NaturalIsomorphism using (NaturalIsomorphism; NI-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Relations using (EquivalenceRelation)

CAT : ∀ {o ℓ e : Level} → Category {suc (o ⊔ ℓ ⊔ e)} {o ⊔ ℓ ⊔ e} {o ⊔ ℓ ⊔ e}
CAT {o} {ℓ} {e} = record
  { Obj = Category {o} {ℓ} {e}
  ; _⇒_ = Functor
  ; _≈_ = NaturalIsomorphism
  ; id = λ {ℂ} → Idᶠ ℂ
  ; _∘_ = _∘ᶠ_
  ; ≈-equiv = NI-equiv
  ; assoc = record
    { F~>G = {! !}
    ; G~>F = {! !}
    ; isomorphism = {! !}
    }
  ; identityˡ = {! !}
  ; identityʳ = {! !}
  ; ∘-resp-≈ = {! !}
  }
