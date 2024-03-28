module Project.Control.NaturalTransformation.Theorems where

open import Level using (Level; levelOfTerm; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
-- open module ≡-Reasoning {n} {A} =
--        EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
--          using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Categories.Cat using (CAT)
module CAT = Category CAT
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; _∘ᶠ_)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_; _∘ᵥ_)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Relations using (EquivalenceRelation)

private
  variable
    o₁ ℓ₁ e₁ : Level
    o₂ ℓ₂ e₂ : Level
    o₃ ℓ₃ e₃ : Level
    ℂ : Category {o₁} {ℓ₁} {e₁}
    𝔻 : Category {o₂} {ℓ₂} {e₂}
    𝔼 : Category {o₃} {ℓ₃} {e₃}

interchange : {F F′ F′′ : Functor ℂ 𝔻}
              {G G′ G′′ : Functor 𝔻 𝔼}
              (α  : F  ~> F′ )
              (α′ : F′ ~> F′′)
              (β  : G  ~> G′ )
              (β′ : G′ ~> G′′) →
              CAT [ ? -- (β′ ∘ᵥ β ) ∘ₕ (α′ ∘ᵥ α)
                  ≈ ? -- (β′ ∘ₕ α′) ∘ᵥ (β  ∘ₕ α)
                  ]
interchange {ℂ = ℂ} {𝔻 = 𝔻} {𝔼 = 𝔼}
            {F = F} {F′ = F′} {F′′ = F′′}
            {G = G} {G′ = G′} {G′′ = G′′}
            α α′ β β′ =
  ?
  -- begin
  --   (β′ ∘ᵥ β ) ∘ₕ (α′ ∘ᵥ α)
  -- ∼⟨ ? ⟩
  --   (β′ ∘ₕ α′) ∘ᵥ (β  ∘ₕ α)
  -- ∎
  where
    module ℂ   = Category ℂ
    module 𝔻   = Category 𝔻
    module 𝔼   = Category 𝔼
    module F   = Functor F
    module F′  = Functor F′
    module F′′ = Functor F′′
    module G   = Functor G
    module G′  = Functor G′
    module G′′ = Functor G′′
    module α   = NaturalTransformation α
    module α′  = NaturalTransformation α′
    module β   = NaturalTransformation β
    module β′  = NaturalTransformation β′
    open module ≈-Reasoning {n} {F G} =
           EquationalReasoning.Core {n} {Functor F G} CAT._≈_ {{CAT.≈-equiv}}
             using (begin_; _∼⟨⟩_; step-∼; _∎)
