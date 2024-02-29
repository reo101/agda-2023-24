module Project.Functor where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import Lib.Equality using (_≡_; refl)

open import Project.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_])

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record Functor (C : Category {o} {ℓ} {e}) (D : Category {o′} {ℓ′} {e′}) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private module C = Category C
  private module D = Category D

  -- field
  --   F₀ : C.Obj → D.Obj
  --   F₁ : ∀ {A B} (f : C [ A , B ]) → D [ F₀ A , F₀ B ]
  --
  --   identity     : ∀ {A}
  --                  → D [ F₁ (C.id {A}) ≈ D.id ]
  --   homomorphism : ∀ {X Y Z}
  --                  {f : C [ X , Y ]}
  --                  {g : C [ Y , Z ]}
  --                  →   D [ F₁ (C [ g ∘ f ])
  --                    ≈ D [ F₁ g ∘ F₁ f ] ]
  --   F-resp-≈     : ∀ {A B}
  --                  {f g : C [ A , B ]}
  --                  → C [    f ≈    g ]
  --                  → D [ F₁ f ≈ F₁ g ]
  --
  -- -- nice shorthands
  -- ₀ = F₀
  -- ₁ = F₁

  field
    F[_] : C.Obj →
           D.Obj
    fmap : ∀ {A B} →
           C [    A   ,    B   ] →
           D [ F[ A ] , F[ B ] ]

  ------------
  --- LAWS ---
  ------------
  field
    identity     : ∀ {A} →
                   D [ fmap (C.id {A}) ≈ D.id ]
    homomorphism : ∀ {X Y Z}
                   {f : C [ X , Y ]}
                   {g : C [ Y , Z ]} →
                   D [ fmap (C [      g ∘      f ])
                     ≈       D [ fmap g ∘ fmap f ]
                     ]
    F-resp-≈     : ∀ {A B}
                   {f g : C [ A , B ]} →
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

HomFunctor : (C : Category {o} {ℓ} {e}) → Set (o ⊔ ℓ ⊔ e)
HomFunctor C = Functor C C

private
  open import Project.Categories using (HASK)

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A
  open Maybe

  maybeFunctor : HomFunctor HASK
  maybeFunctor =
    record
      { F[_] = Maybe
      ; fmap = λ f → λ { nothing → nothing; (just x) → just (f x) }
      ; identity = λ { {A} → ? }
      ; homomorphism = {! !}
      ; F-resp-≈ = {! !} }

private
  op-involutive :
    {C : Category {o} {ℓ} {e}}
    {D : Category {o′} {ℓ′} {e′}} →
    (F : Functor C D) →
    Functor.op (Functor.op F) ≡ F
  op-involutive _ = refl
