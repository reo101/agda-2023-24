module Project.Control.Adjunction where

open import Level using (Level; levelOfTerm; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
-- open module ≡-Reasoning {n} {A} =
--        EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
--          using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Categories.Cat using (CAT)
module CAT = Category CAT
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; fmap; _∘ᶠ_; _²) renaming (Id to Idᶠ)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)
open import Project.Control.Monad using (Monad)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Relations using (EquivalenceRelation)

private
  variable
    o₁ ℓ₁ e₁ : Level
    o₂ ℓ₂ e₂ : Level

-- NOTE: modeled as a counit-unit adjunction

record Adjunction (ℂ : Category {o₁} {ℓ₁} {e₁})
                  (𝔻 : Category {o₂} {ℓ₂} {e₂})
                  (L : Functor 𝔻 ℂ)
                  (R : Functor ℂ 𝔻)
       : Set (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  private module ℂ = Category ℂ
  private module 𝔻 = Category 𝔻
  private module L = Functor L
  private module R = Functor R

  field
    ε : L ∘ᶠ R ~> Idᶠ ℂ
    η : Idᶠ 𝔻 ~> R ∘ᶠ L

  module ε = NaturalTransformation ε
  module η = NaturalTransformation η

  ------------
  --- LAWS ---
  ------------
  field
    identityL : ∀ {B : 𝔻.Obj} →
                ℂ [ ℂ [ L [fmap η.component B ] ∘ ε.component (L [ B ]) ]
                  ≈ ℂ.id
                  ]

    identityR : ∀ {A : ℂ.Obj} →
                𝔻 [ 𝔻 [ η.component (R [ A ]) ∘ R [fmap ε.component A ] ]
                  ≈ 𝔻.id
                  ]

open Adjunction

module Helpers where
  _⊣_ : {ℂ : Category {o₁} {ℓ₁} {e₁}}
        {𝔻 : Category {o₂} {ℓ₂} {e₂}}
        (L : Functor 𝔻 ℂ)
        (R : Functor ℂ 𝔻) →
        Set _
  _⊣_ {ℂ = ℂ} {𝔻 = 𝔻} L R = Adjunction ℂ 𝔻 L R

  monadFromAdjunction : {ℂ : Category {o₁} {ℓ₁} {e₁}}
                        {𝔻 : Category {o₁} {ℓ₁} {e₁}}
                        {L : Functor 𝔻 ℂ}
                        {R : Functor ℂ 𝔻}
                        (L⊣R : L ⊣ R) →
                        Monad 𝔻
  monadFromAdjunction {ℂ = ℂ} {𝔻 = 𝔻} {L = L} {R = R} L⊣R = record
    { F = R ∘ᶠ L
    ; η = L⊣R.η
    ; μ = record
      { component = {! !}
      ; commutativity = {! !}
      }
    ; μμ-associative = {! !}
    ; μη-associative = {! !}
    ; μη-identity = {! !}
    }
    where
      module ℂ = Category ℂ
      module 𝔻 = Category 𝔻
      module L = Functor L
      module R = Functor R
      module L⊣R = Adjunction L⊣R
      open module ≈-Reasoning {n} {A} {B} =
             EquationalReasoning.Core CAT._≈_ {{CAT.≈-equiv {A} {B}}}
               using (begin_; _∼⟨⟩_; step-∼; _∎;
                      reflexive; symmetric; transitive)

open Helpers public
