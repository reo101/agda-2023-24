{-# OPTIONS --allow-unsolved-metas #-}

module Project.NaturalTransformation where

open import Level using (Level; levelOfTerm; _⊔_)

open import Lib.Equality using (_≡_; refl)
open import Lib.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎; sym; cong; cong-app; trans; subst)

open import Project.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Functor using (Functor; HomFunctor; _[_]; _[fmap_]) renaming (_∘_ to _∘F_)
open import Project.Postulates using (funext)

private
  variable
    o₁ ℓ₁ e₁ : Level
    o₂ ℓ₂ e₂ : Level
    o₃ ℓ₃ e₃ : Level


record NaturalTransformation (ℂ : Category {o₁} {ℓ₁} {e₁})
                             (𝔻 : Category {o₂} {ℓ₂} {e₂})
                             (F G : Functor ℂ 𝔻)
       : Set (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  private module ℂ = Category ℂ
  private module 𝔻 = Category 𝔻
  private module F = Functor F
  private module G = Functor G

  field
    component : ∀ (X) →
                𝔻 [ F [ X ] , G [ X ] ]

  ------------
  --- LAWS ---
  ------------
  field
    commutativity : ∀ {X Y}
                    {f : ℂ [ X , Y ]} →
                    𝔻 [ 𝔻 [ G [fmap f ] ∘ component X ]
                      ≈ 𝔻 [ component Y ∘ F [fmap f ] ]
                      ]

module Helpers where
  private
    variable
      ℂ : Category {o₁} {ℓ₁} {e₁}
      𝔻 : Category {o₂} {ℓ₂} {e₂}
      𝔼 : Category {o₃} {ℓ₃} {e₃}

  _~>_ : (F G : Functor ℂ 𝔻) →
         Set _
  _~>_ {ℂ = ℂ} {𝔻 = 𝔻} F G = NaturalTransformation ℂ 𝔻 F G
  infixr 15 _~>_

  _∘ᵥ_ : {F G H : Functor ℂ 𝔻} →
         G ~> H →
         F ~> G →
         F ~> H
  _∘ᵥ_ {ℂ = ℂ} {𝔻 = 𝔻} β α = record
    { component = λ { x → β.component x ∘ α.component x }
    ; commutativity = {! !}
    }
    where
      open Category 𝔻 using (_∘_)
      module α = NaturalTransformation α
      module β = NaturalTransformation β

  _∘ₕ_ : {F F' : Functor ℂ 𝔻}
         {G G' : Functor 𝔻 𝔼} →
         F ~> F' →
         G ~> G' →
         G ∘F F ~> G' ∘F F'
  _∘ₕ_ {ℂ = ℂ} {𝔻 = 𝔻} {𝔼 = 𝔼} {F = F} {F' = F'} {G = G} {G' = G'} β α = record
    { component = λ { x → ? ∘ ? }
    ; commutativity = {! kek !}
    }
    where
      open Category 𝔼 using (_∘_)
      module F  = Functor F
      module F' = Functor F'
      module G  = Functor G
      module G' = Functor G'
      module α  = NaturalTransformation α
      module β  = NaturalTransformation β

  -- TODO: `funext` for morhpisms
  --       `≈-Reasoning` ?
  Id : {ℂ : Category {o₁} {ℓ₁} {e₁}}
       {𝔻 : Category {o₂} {ℓ₂} {e₂}}
       (F : Functor ℂ 𝔻) →
       F ~> F
  Id {ℂ = ℂ} F = record
    { component = λ { X → F [fmap Category.id ℂ ] }
    ; commutativity = λ { {X} {Y} {f} →
        ?
        -- begin
        --   𝔻 [ 𝔻 [ F [fmap f ] ∘ F [fmap Category.id ℂ ] ]
        -- ≈⟨ ? ⟩
        --   𝔻 [ F [fmap Category.id ℂ ] ∘ F [fmap f ] ] ]
        -- ∎
      }
    }

  IdHASK : (F : HomFunctor HASK) →
           F ~> F
  IdHASK F = record
    { component = λ { X → F [fmap ℂⁱᵈ ] }
    ; commutativity = λ { {f = f} → funext (λ { x →
        begin
          (F [fmap f ]) ((F [fmap ℂⁱᵈ ]) x)
        ≡⟨ cong (F [fmap f ]) (cong-app Fⁱᵈ _) ⟩ -- _ ≡ x
          (F [fmap f ]) (ℂⁱᵈ x)
        ≡⟨⟩
          (F [fmap f ]) x
        ≡⟨⟩
          ℂⁱᵈ ((F [fmap f ]) x)
        ≡⟨ cong-app (sym Fⁱᵈ) _ ⟩ -- _ ≡ ((F [fmap f ]) x)
          (F [fmap ℂⁱᵈ ]) ((F [fmap f ]) x)
        ∎
      }) }
    }
    where
      open Category HASK renaming (id to ℂⁱᵈ)
      open Functor F renaming (identity to Fⁱᵈ)

open Helpers public
