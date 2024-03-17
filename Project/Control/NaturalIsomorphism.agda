module Project.Control.NaturalIsomorphism where

open import Level using (Level; levelOfTerm; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
-- open module ≡-Reasoning {n} {A} =
--        EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
--          using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_]; _∘ᶠ_)
open import Project.Control.NaturalTransformation using (NaturalTransformation; _~>_; _∘ₕ_; _∘ᵥ_) renaming (Id to Idⁿ)
open import Project.Control.Isomorphism using (Isomorphism)
open import Project.EquationalReasoning as EquationalReasoning
open import Project.Postulates using (funext)
open import Project.Relations using (EquivalenceRelation)

private
  variable
    o₁ ℓ₁ e₁ : Level
    o₂ ℓ₂ e₂ : Level

record NaturalIsomorphism {ℂ : Category {o₁} {ℓ₁} {e₁}}
                          {𝔻 : Category {o₂} {ℓ₂} {e₂}}
                          (F G : Functor ℂ 𝔻)
       : Set (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  eta-equality

  private module ℂ = Category ℂ
  private module 𝔻 = Category 𝔻
  private module F = Functor F
  private module G = Functor G

  field
    F~>G : F ~> G
    G~>F : G ~> F

  module F~>G = NaturalTransformation F~>G
  module G~>F = NaturalTransformation G~>F

  ------------
  --- LAWS ---
  ------------
  field
    isomorphism : ∀ {X : ℂ.Obj} →
                  Isomorphism 𝔻 {A = F [ X ]} {B = G [ X ]}
                    (F~>G.component X)
                    (G~>F.component X)

  module isomorphism {X} = Isomorphism (isomorphism {X})

module Helpers where
  private
    variable
      ℂ : Category {o₁} {ℓ₁} {e₁}
      𝔻 : Category {o₂} {ℓ₂} {e₂}

  NI-equiv : EquivalenceRelation (NaturalIsomorphism {ℂ = ℂ} {𝔻 = 𝔻})
  NI-equiv {ℂ = ℂ} {𝔻 = 𝔻} = record
    { reflexive = λ {F} →
      let module F = Functor F
      in record
        { F~>G = Idⁿ F
        ; G~>F = Idⁿ F
        ; isomorphism = λ {X} → record
          { isomorphismˡ =
            begin
              𝔻 [ F [fmap ℂ.id ] ∘ F [fmap ℂ.id ] ]
            ∼⟨ symmetric (𝔻.∘-resp-≈ (symmetric F.identity) (symmetric F.identity)) ⟩
              𝔻 [ 𝔻.id ∘ 𝔻.id ]
            ∼⟨ 𝔻.identityˡ ⟩
              𝔻.id
            ∎
          ; isomorphismʳ =
            begin
              𝔻 [ F [fmap ℂ.id ] ∘ F [fmap ℂ.id ] ]
            ∼⟨ symmetric (𝔻.∘-resp-≈ (symmetric F.identity) (symmetric F.identity)) ⟩
              𝔻 [ 𝔻.id ∘ 𝔻.id ]
            ∼⟨ 𝔻.identityˡ ⟩
              𝔻.id
            ∎
          }
        }
    ; symmetric = λ { {F} {G} α →
      let module F = Functor F
          module G = Functor G
          module α = NaturalIsomorphism α
       in record
        { F~>G = α.G~>F
        ; G~>F = α.F~>G
        ; isomorphism = λ {X} → record
          { isomorphismˡ = α.isomorphism.isomorphismʳ
          ; isomorphismʳ = α.isomorphism.isomorphismˡ
          }
        }
      }
    ; transitive = λ { {F} {G} {H} α β →
      let module F = Functor F
          module G = Functor G
          module H = Functor H
          module α = NaturalIsomorphism α
          module β = NaturalIsomorphism β
       in record
        { F~>G = β.F~>G ∘ᵥ α.F~>G
        ; G~>F = α.G~>F ∘ᵥ β.G~>F
        ; isomorphism = λ {X} → record
          { isomorphismˡ =
            begin
              𝔻 [ 𝔻 [ α.G~>F.component X
                    ∘ β.G~>F.component X
                    ]
                ∘ 𝔻 [ β.F~>G.component X
                    ∘ α.F~>G.component X
                    ]
                ]
            ∼⟨ 𝔻.assoc ⟩
              𝔻 [ α.G~>F.component X
                ∘ 𝔻 [ β.G~>F.component X
                    ∘ 𝔻 [ β.F~>G.component X
                        ∘ α.F~>G.component X
                        ]
                    ]
                ]
            ∼⟨ 𝔻.∘-resp-≈ reflexive (symmetric 𝔻.assoc) ⟩
              𝔻 [ α.G~>F.component X
                ∘ 𝔻 [ 𝔻 [ β.G~>F.component X
                        ∘ β.F~>G.component X
                        ]
                    ∘ α.F~>G.component X
                    ]
                ]
            ∼⟨ 𝔻.∘-resp-≈ reflexive (𝔻.∘-resp-≈ β.isomorphism.isomorphismˡ reflexive) ⟩
              𝔻 [ α.G~>F.component X
                ∘ 𝔻 [ 𝔻.id
                    ∘ α.F~>G.component X
                    ]
                ]
            ∼⟨ 𝔻.∘-resp-≈ reflexive 𝔻.identityˡ ⟩
              𝔻 [ α.G~>F.component X
                ∘ α.F~>G.component X
                ]
            ∼⟨ α.isomorphism.isomorphismˡ ⟩
              𝔻.id
            ∎
          ; isomorphismʳ =
            begin
              𝔻 [ 𝔻 [ β.F~>G.component X
                    ∘ α.F~>G.component X
                    ]
                ∘ 𝔻 [ α.G~>F.component X
                    ∘ β.G~>F.component X
                    ]
                ]
            ∼⟨ 𝔻.assoc ⟩
              𝔻 [ β.F~>G.component X
                ∘ 𝔻 [ α.F~>G.component X
                    ∘ 𝔻 [ α.G~>F.component X
                        ∘ β.G~>F.component X
                        ]
                    ]
                ]
            ∼⟨ 𝔻.∘-resp-≈ reflexive (symmetric 𝔻.assoc) ⟩
              𝔻 [ β.F~>G.component X
                ∘ 𝔻 [ 𝔻 [ α.F~>G.component X
                        ∘ α.G~>F.component X
                        ]
                    ∘ β.G~>F.component X
                    ]
                ]
            ∼⟨ 𝔻.∘-resp-≈ reflexive (𝔻.∘-resp-≈ α.isomorphism.isomorphismʳ reflexive) ⟩
              𝔻 [ β.F~>G.component X
                ∘ 𝔻 [ 𝔻.id
                    ∘ β.G~>F.component X
                    ]
                ]
            ∼⟨ 𝔻.∘-resp-≈ reflexive 𝔻.identityˡ ⟩
              𝔻 [ β.F~>G.component X
                ∘ β.G~>F.component X
                ]
            ∼⟨ β.isomorphism.isomorphismʳ ⟩
              𝔻.id
            ∎
          }
        }
      }
    }
    where
      module ℂ = Category ℂ
      module 𝔻 = Category 𝔻
      open module ≈-Reasoning {A} {B} =
             EquationalReasoning.Core 𝔻._≈_ {{𝔻.≈-equiv {A} {B}}}
               using (begin_; _∼⟨⟩_; step-∼; _∎;
                      reflexive; symmetric; transitive)

open Helpers public
