module Project.Control.NaturalTransformation where

open import Level using (Level; levelOfTerm; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
-- open module ≡-Reasoning {n} {A} =
--        EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
--          using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; _∘ᶠ_)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Relations using (EquivalenceRelation)

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
  _∘ᵥ_ {ℂ = ℂ} {𝔻 = 𝔻} {F = F} {G = G} {H = H} β α = record
    { component = λ { x → 𝔻 [ β.component x ∘ α.component x ] }
    ; commutativity = λ { {X} {Y} {f} →
        begin
          𝔻 [ H [fmap f ]
            ∘ 𝔻 [ β.component X ∘ α.component X ]
            ]
        ∼⟨ ? ⟩
          𝔻 [ 𝔻 [ β.component Y ∘ α.component Y ]
            ∘ F [fmap f ]
            ]
        ∎
      }
    }
    where
      module 𝔻 = Category 𝔻
      module F = Functor F
      module G = Functor G
      module H = Functor H
      module α = NaturalTransformation α
      module β = NaturalTransformation β
      open module ≈-Reasoning {A} {B} =
             EquationalReasoning.Core 𝔻._≈_ {{𝔻.≈-equiv {A} {B}}}
               using (begin_; _∼⟨⟩_; step-∼; _∎;
                      reflexive; symmetric; transitive)

  _∘ₕ_ : {F F′ : Functor ℂ 𝔻}
         {G G′ : Functor 𝔻 𝔼} →
         G ~> G′ →
         F ~> F′ →
         G ∘ᶠ F ~> G′ ∘ᶠ F′
  _∘ₕ_ {ℂ = ℂ} {𝔻 = 𝔻} {𝔼 = 𝔼}
       {F = F} {F′ = F′}
       {G = G} {G′ = G′}
       β α = record
    { component = λ { a → 𝔼 [ G′ [fmap α.component a ] ∘ β.component (F [ a ]) ] }
    ; commutativity = λ { {a} {b} {f} →
         begin
           𝔼 [ G′ [fmap F′ [fmap f ] ]
             ∘ 𝔼 [ G′ [fmap α.component a ] ∘ β.component (F [ a ]) ]
             ]
         ∼⟨ symmetric 𝔼.assoc ⟩
           𝔼 [ 𝔼 [ G′ [fmap F′ [fmap f ] ] ∘ G′ [fmap α.component a ] ]
             ∘ β.component (F [ a ])
             ]
         ∼⟨ 𝔼.∘-resp-≈ (symmetric G′.homomorphism) reflexive ⟩
           𝔼 [ G′ [fmap 𝔻 [ F′ [fmap f ] ∘ α.component a ] ]
             ∘ β.component (F [ a ])
             ]
         ∼⟨ β.commutativity ⟩
           𝔼 [ β.component (F′ [ b ])
             ∘ G [fmap 𝔻 [ F′ [fmap f ] ∘ α.component a ] ]
             ]
         ∼⟨ 𝔼.∘-resp-≈ reflexive (G.F-resp-≈ α.commutativity) ⟩
           𝔼 [ β.component (F′ [ b ])
             ∘ G [fmap 𝔻 [ α.component b ∘ F [fmap f ] ] ]
             ]
         ∼⟨ 𝔼.∘-resp-≈ reflexive G.homomorphism ⟩
           𝔼 [ β.component (F′ [ b ])
             ∘ 𝔼 [ G [fmap α.component b ] ∘ G [fmap F [fmap f ] ] ]
             ]
         ∼⟨ symmetric 𝔼.assoc ⟩
           𝔼 [ 𝔼 [ β.component (F′ [ b ]) ∘ G [fmap α.component b ] ]
             ∘ G [fmap F [fmap f ] ]
             ]
         ∼⟨ 𝔼.∘-resp-≈ (symmetric β.commutativity) reflexive ⟩
           𝔼 [ 𝔼 [ G′ [fmap α.component b ] ∘ β.component (F [ b ]) ]
             ∘ G [fmap F [fmap f ] ]
             ]
         ∎
      }
    }
    where
      module ℂ = Category ℂ
      module 𝔻 = Category 𝔻
      module 𝔼 = Category 𝔼
      module F  = Functor F
      module F′ = Functor F′
      module G  = Functor G
      module G′ = Functor G′
      module α  = NaturalTransformation α
      module β  = NaturalTransformation β
      open module ≈-Reasoning {A} {B} =
             EquationalReasoning.Core 𝔼._≈_ {{𝔼.≈-equiv {A} {B}}}
               using (begin_; _∼⟨⟩_; step-∼; _∎;
                      reflexive; symmetric; transitive)

  interchange : {F F′ F′′ : Functor ℂ 𝔻}
                {G G′ G′′ : Functor 𝔻 𝔼}
                (α  : F  ~> F′ )
                (α′ : F′ ~> F′′)
                (β  : G  ~> G′ )
                (β′ : G′ ~> G′′) →
                (β′ ∘ᵥ β ) ∘ₕ (α′ ∘ᵥ α) ≡
                (β′ ∘ₕ α′) ∘ᵥ (β  ∘ₕ α)
  interchange {ℂ = ℂ} {𝔻 = 𝔻} {𝔼 = 𝔼}
              {F = F} {F′ = F′} {F′′ = F′′}
              {G = G} {G′ = G′} {G′′ = G′′}
              α α′ β β′ =
    begin
      (β′ ∘ᵥ β ) ∘ₕ (α′ ∘ᵥ α)
    ∼⟨ ? ⟩
      (β′ ∘ₕ α′) ∘ᵥ (β  ∘ₕ α)
    ∎
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
      open module ≡-Reasoning {n} {A} =
             EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
               using (begin_; _∼⟨⟩_; step-∼; _∎)


  Id : {ℂ : Category {o₁} {ℓ₁} {e₁}}
       {𝔻 : Category {o₂} {ℓ₂} {e₂}}
       (F : Functor ℂ 𝔻) →
       F ~> F
  Id {ℂ = ℂ} {𝔻 = 𝔻} F = record
    { component = λ { X → F [fmap ℂ.id ] }
    ; commutativity = λ { {X = X} {Y = Y} {f = f} →
        begin
          𝔻 [ F [fmap f ] ∘ F [fmap ℂ.id ] ]
        ∼⟨ 𝔻.∘-resp-≈ reflexive F.identity ⟩
          𝔻 [ F [fmap f ] ∘ 𝔻.id ]
        ∼⟨ 𝔻.identityʳ ⟩
          F [fmap f ]
        ∼⟨ symmetric 𝔻.identityˡ ⟩
          𝔻 [ 𝔻.id ∘ F [fmap f ] ]
        ∼⟨ 𝔻.∘-resp-≈ (symmetric F.identity) reflexive ⟩
          𝔻 [ F [fmap ℂ.id ] ∘ F [fmap f ] ]
        ∎
        -- begin
        --   𝔻 [                  F [fmap f ] ∘ F [fmap ℂ.id ] ]
        -- ∼⟨ 𝔻.∘-resp-≈ reflexive F.identity ⟩
        --   𝔻 [                  F [fmap f ] ∘ 𝔻.id           ]
        -- ∼⟨ 𝔻.identityʳ ⟩
        --                        F [fmap f ]
        -- ∼⟨ symmetric 𝔻.identityˡ ⟩
        --   𝔻 [           𝔻.id ∘ F [fmap f ]                  ]
        -- ∼⟨ 𝔻.∘-resp-≈ (symmetric F.identity) reflexive ⟩
        --   𝔻 [ F [fmap ℂ.id ] ∘ F [fmap f ]                  ]
        -- ∎
      }
    }
    where
      module ℂ = Category ℂ
      module 𝔻 = Category 𝔻
      module F = Functor F
      open module ≈-Reasoning {A} {B} =
             EquationalReasoning.Core 𝔻._≈_ {{𝔻.≈-equiv {A} {B}}}
               using (begin_; _∼⟨⟩_; step-∼; _∎;
                      reflexive; symmetric; transitive)

open Helpers public
