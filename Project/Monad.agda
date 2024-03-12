module Project.Monad where

open import Level using (Level; zero; suc; _⊔_)

open import Lib.Equality using (_≡_; refl)
open import Lib.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎; sym; cong; cong-app; trans; subst)

open import Project.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Project.Functor using (Functor; HomFunctor; _[_]; fmap; _²; Id)
open import Project.NaturalTransformation using (NaturalTransformation; _~>_)
open import Project.Postulates using (funext)

private
  variable
    o ℓ e : Level

record Monad (ℂ : Category {o} {ℓ} {e}) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : HomFunctor ℂ
    η : Id ℂ ~> F
    μ : F ² ~> F

  private module ℂ = Category ℂ
  private module F = Functor F

  ------------
  --- LAWS ---
  ------------
  -- field
  -- TODO: whiskering
  -- μ ∘ Fμ = μ ∘ μF
  -- μ ∘ Fη = μ ∘ ηF = Idₙₐₜ
    --
    -- identity     : ∀ {X} →
    --                𝔻 [ fmap (ℂ.id {X})
    --                  ≈       𝔻.id
    --                  ]
    --
    -- homomorphism : ∀ {X Y Z}
    --                {f : ℂ [ X , Y ]}
    --                {g : ℂ [ Y , Z ]} →
    --                𝔻 [ fmap (ℂ [      g ∘      f ])
    --                  ≈       𝔻 [ fmap g ∘ fmap f ]
    --                  ]
    --
    -- F-resp-≈     : ∀ {X Y}
    --                {f g : ℂ [ X , Y ]} →
    --                ℂ [      f ≈      g ] →
    --                𝔻 [ fmap f ≈ fmap g ]

-- private
--   op-involutive :
--     {ℂ : Category {o₁} {ℓ₁} {e₁}}
--     {𝔻 : Category {o₂} {ℓ₂} {e₂}}
--     {F : Functor ℂ D} →
--     Functor.op (Functor.op F) ≡ F
--   op-involutive = refl
