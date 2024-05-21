module Project.Control.Monad where

open import Level using (Level; zero; suc; _⊔_)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; fmap; _²) renaming (Id to Idᶠ)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_) renaming (Id to Idⁿ)

private
  variable
    o ℓ e : Level

record Monad (ℂ : Category {o} {ℓ} {e}) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : HomFunctor ℂ
    η : Idᶠ ℂ ~> F
    μ : F ² ~> F

  module ℂ = Category ℂ
  module F = Functor F
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ

  ------------
  --- LAWS ---
  ------------
  field
    -- μ ∘ Fμ = μ ∘ μF
    μμ-associative : ∀ {X} →
                     ℂ [ ℂ [ μ.component X ∘ μ.component (F [ X ]) ]
                       ≈ ℂ [ μ.component X ∘ F [fmap μ.component X ] ]
                       ]

    -- μ ∘ Fη = μ ∘ ηF = Idᶠ
    μη-associative : ∀ {X} →
                     ℂ [ ℂ [ μ.component X ∘ η.component (F [ X ]) ]
                       ≈ ℂ [ μ.component X ∘ F [fmap η.component X ] ]
                       ]
    μη-identity : ∀ {X} →
                  ℂ [ ℂ [ μ.component X ∘ η.component (F [ X ]) ]
                    ≈ ℂ.id
                    ]

-- TODO: make generic over ℂ
-- module Helpers {ℂ : Category {o} {ℓ} {e}} {{m : Monad ℂ}} where
open import Project.Control.Categories using (HASK)
module Helpers {{m : Monad HASK}} where
  open Monad m using (F; μ)
  open import Lib.Utils using (const)

  private
    variable
      -- A B : Category.Obj ℂ
      A B : Category.Obj HASK

  _>>=_ : F [ A ] → (A → F [ B ]) → F [ B ]
  _>>=_ {B = B} mx f = μ.component B ((F [fmap f ]) mx)

  _>>_ : F [ A ] → F [ B ] → F [ B ]
  _>>_ {B = B} mx my = μ.component B ((F [fmap const my ]) mx)

open Helpers public
