module Project.Functor where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import Lib.Equality using (_≡_; refl)
open import Lib.≡-Reasoning using (cong; cong-app)

open import Project.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Project.Postulates using (funext)

private
  variable
    o₁ ℓ₁ e₁ : Level
    o₂ ℓ₂ e₂ : Level

record Functor (C : Category {o₁} {ℓ₁} {e₁}) (D : Category {o₂} {ℓ₂} {e₂}) : Set (o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
  eta-equality
  private module C = Category C
  private module D = Category D

  field
    -- Mapping of objects to objects
    F[_] : C.Obj →
           D.Obj

    -- Mapping of morphisms to morphisms
    fmap : ∀ {A B} →
           C [    A   ,    B   ] →
           D [ F[ A ] , F[ B ] ]

  ------------
  --- LAWS ---
  ------------
  field
    identity     : ∀ {X} →
                   D [ fmap (C.id {X})
                     ≈       D.id
                     ]

    homomorphism : ∀ {X Y Z}
                   {f : C [ X , Y ]}
                   {g : C [ Y , Z ]} →
                   D [ fmap (C [      g ∘      f ])
                     ≈       D [ fmap g ∘ fmap f ]
                     ]

    F-resp-≈     : ∀ {X Y}
                   {f g : C [ X , Y ]} →
                   C [      f ≈      g ] →
                   D [ fmap f ≈ fmap g ]

  op : Functor C.op D.op
  op = record
    { F[_]         = F[_]
    ; fmap         = fmap
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }

HomFunctor : (C : Category {o₁} {ℓ₁} {e₁}) → Set (o₁ ⊔ ℓ₁ ⊔ e₁)
HomFunctor C = Functor C C

private
  open import Project.Categories using (HASK)

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A
  open Maybe

  maybeFunctor : HomFunctor HASK
  maybeFunctor = record
    { F[_] = Maybe
    ; fmap = λ f →
        λ { nothing → nothing
          ; (just x) → just (f x)
          }
    ; identity =
        funext (λ { nothing → refl
                  ; (just x) → refl
                  })
    ; homomorphism =
        funext (λ { nothing → refl
                  ; (just x) → refl
                  })
    ; F-resp-≈ = λ C[f≈g] →
        funext (λ { nothing → refl
                  ; (just x) → cong just (cong-app C[f≈g] x)
                  })
    }

private
  op-involutive :
    {C : Category {o₁} {ℓ₁} {e₁}}
    {D : Category {o₂} {ℓ₂} {e₂}}
    {F : Functor C D} →
    Functor.op (Functor.op F) ≡ F
  op-involutive = refl
