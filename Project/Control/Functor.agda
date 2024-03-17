module Project.Control.Functor where

open import Level using (Level; zero; suc; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
-- open module ≡-Reasoning {n} {A} =
--        EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
--          using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Lib.Utils renaming (_∘_ to _∘ₐ_)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Project.Postulates using (funext)

private
  variable
    o₁ ℓ₁ e₁ : Level
    o₂ ℓ₂ e₂ : Level
    o₃ ℓ₃ e₃ : Level
    o₄ ℓ₄ e₄ : Level

record Functor (ℂ : Category {o₁} {ℓ₁} {e₁})
               (𝔻 : Category {o₂} {ℓ₂} {e₂})
       : Set (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  eta-equality

  private module ℂ = Category ℂ
  private module 𝔻 = Category 𝔻

  field
    -- Mapping of objects to objects
    F[_] : ℂ.Obj →
           𝔻.Obj

    -- Mapping of morphisms to morphisms
    fmap : ∀ {A B} →
           ℂ [    A   ,    B   ] →
           𝔻 [ F[ A ] , F[ B ] ]

  ------------
  --- LAWS ---
  ------------
  field
    identity     : ∀ {X} →
                   𝔻 [ fmap (ℂ.id {X})
                     ≈       𝔻.id
                     ]

    homomorphism : ∀ {X Y Z}
                   {f : ℂ [ X , Y ]}
                   {g : ℂ [ Y , Z ]} →
                   𝔻 [ fmap (ℂ [      g ∘      f ])
                     ≈       𝔻 [ fmap g ∘ fmap f ]
                     ]

    F-resp-≈     : ∀ {X Y}
                   {f g : ℂ [ X , Y ]} →
                   ℂ [      f ≈      g ] →
                   𝔻 [ fmap f ≈ fmap g ]

  op : Functor ℂ.op 𝔻.op
  op = record
    { F[_]         = F[_]
    ; fmap         = fmap
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }

open Functor public

module Helpers where
  private
    variable
      ℂ : Category {o₁} {ℓ₁} {e₁}
      𝔻 : Category {o₂} {ℓ₂} {e₂}
      𝔼 : Category {o₃} {ℓ₃} {e₃}

  _[_] : (F : Functor ℂ 𝔻) →
         let private module ℂ = Category ℂ
             private module 𝔻 = Category 𝔻
          in ℂ.Obj → 𝔻.Obj
         -- Category.Obj ℂ →
         -- Category.Obj 𝔻
  _[_] = Functor.F[_]

  _[fmap_] : (F : Functor ℂ 𝔻) →
             ∀ {A B} →
             ℂ [     A   ,     B   ] →
             𝔻 [ F [ A ] , F [ B ] ]
  _[fmap_] = Functor.fmap

  HomFunctor : (ℂ : Category {o₁} {ℓ₁} {e₁}) → Set (o₁ ⊔ ℓ₁ ⊔ e₁)
  HomFunctor ℂ = Functor ℂ ℂ

  Id : (ℂ : Category {o₁} {ℓ₁} {e₁}) → Functor ℂ ℂ
  Id ℂ = record
    { F[_] = id
    ; fmap = id
    ; identity = λ { {X} →
        begin
          ℂ.id
        ∎
      }
    ; homomorphism = λ { {X} {Y} {Z} {f} {g} →
        begin
          ℂ [ g ∘ f ]
        ∎
      }
    ; F-resp-≈ = λ { {X} {Y} {f} {g} ℂ[f≈g] →
        begin
          id f
        ∼⟨⟩
          f
        ∼⟨ ℂ[f≈g] ⟩
          g
        ∼⟨⟩
          id g
        ∎
      }
    }
    where
      module ℂ = Category ℂ
      open module ≈-Reasoning {A} {B} =
             EquationalReasoning.Core ℂ._≈_ {{ℂ.≈-equiv {A} {B}}}
               using (begin_; _∼⟨⟩_; step-∼; _∎;
                      reflexive; symmetric; transitive)

  _∘ᶠ_ : Functor 𝔻 𝔼 → Functor ℂ 𝔻 → Functor ℂ 𝔼
  _∘ᶠ_ {𝔻 = 𝔻} {𝔼 = 𝔼} {ℂ = ℂ} G F = record
    { F[_] = λ x → G [ F [ x ] ]
    ; fmap = λ f → G [fmap F [fmap f ] ]
    ; identity = λ { {X} →
        begin
          G [fmap F [fmap ℂ.id ] ]
        ∼⟨ G.F-resp-≈ F.identity ⟩
          G [fmap 𝔻.id ]
        ∼⟨ G.identity ⟩
          𝔼.id
        ∎
      }
    ; homomorphism = λ { {X} {Y} {Z} {f} {g} →
        begin
          G [fmap F [fmap (ℂ [ g ∘ f ]) ] ]
        ∼⟨ G.F-resp-≈ F.homomorphism ⟩
          G [fmap 𝔻 [ F [fmap g ] ∘ F [fmap f ] ] ]
        ∼⟨ G.homomorphism ⟩
          𝔼 [ G [fmap F [fmap g ] ] ∘ G [fmap F [fmap f ] ] ]
        ∎
      }
    ; F-resp-≈ = λ { {X} {Y} {f} {g} ℂ[f≈g] →
        begin
          G [fmap F [fmap f ] ]
        ∼⟨ G.F-resp-≈ (F.F-resp-≈ ℂ[f≈g]) ⟩
          G [fmap F [fmap g ] ]
        ∎
      }
    }
    where
      module F = Functor F
      module G = Functor G
      module ℂ = Category ℂ
      module 𝔻 = Category 𝔻
      module 𝔼 = Category 𝔼
      open module ≈-Reasoning {A} {B} =
             EquationalReasoning.Core 𝔼._≈_ {{𝔼.≈-equiv {A} {B}}}
               using (begin_; _∼⟨⟩_; step-∼; _∎;
                      reflexive; symmetric; transitive)
  infixr 20 _∘ᶠ_

  ∘ᶠ-assoc : {A : Category {o₁} {ℓ₁} {e₁}}
             {B : Category {o₂} {ℓ₂} {e₂}}
             {C : Category {o₃} {ℓ₃} {e₃}}
             {D : Category {o₄} {ℓ₄} {e₄}}
             (F : Functor A B)
             (G : Functor B C)
             (H : Functor C D) →
             (H ∘ᶠ G) ∘ᶠ F ≡ H ∘ᶠ (G ∘ᶠ F)
  ∘ᶠ-assoc {A = A} {B = B} {C = C} {D = D} F G H =
    {! !}
    where
      module A = Category A
      module B = Category B
      module C = Category C
      module D = Category D
      module F = Functor F
      module G = Functor G
      module H = Functor H
      module H∘ᶠG = Functor (H ∘ᶠ G)
      module G∘ᶠF = Functor (G ∘ᶠ F)
      open module ≡-Reasoning {n} {X} =
             EquationalReasoning.Core {n} {X} _≡_ {{≡-equiv}}
               using (begin_; _∼⟨⟩_; step-∼; _∎)

  _² : HomFunctor ℂ → HomFunctor ℂ
  F ² = F ∘ᶠ F

open Helpers public

-- private
--   op-involutive :
--     {ℂ : Category {o₁} {ℓ₁} {e₁}}
--     {𝔻 : Category {o₂} {ℓ₂} {e₂}}
--     {F : Functor ℂ 𝔻} →
--     Functor.op (Functor.op F) ≡ F
--   op-involutive = refl
