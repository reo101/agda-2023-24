module Project.Categories where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

open import Lib.Equality using (_≡_; refl)
open import Lib.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎; trans; sym; cong; cong-app)
open import Lib.Utils using (flip) renaming (_∘_ to _∘ₐ_; id to idₐ)

-- <https://www.cas.mcmaster.ca/~carette/publications/2005.07059.pdf>

private
  variable
    o ℓ e : Level

record Category : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  eta-equality

  infix  4 _⇒_
  infix  4 _≈_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : (A B : Obj) → Set ℓ
    -- TODO: relation of equivalence???
    _≈_ : ∀ {A B} → (f g : A ⇒ B) → Set e

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  ------------
  --- LAWS ---
  ------------
  field
    assoc     : ∀ {A B C D}
                {f : A ⇒ B}
                {g : B ⇒ C}
                {h : C ⇒ D} →
                -----------------------------
                (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

    -- TODO: remove this????
    sym-assoc : ∀ {A B C D}
                {f : A ⇒ B}
                {g : B ⇒ C}
                {h : C ⇒ D} →
                ---------------------------
                h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f

    identityˡ : ∀ {A B}
                {f : A ⇒ B} →
                -----------
                id ∘ f ≈ f

    identityʳ : ∀ {A B}
                {f : A ⇒ B} →
                ----------
                f ∘ id ≈ f

    ∘-resp-≈  : ∀ {A B C}
                {f h : B ⇒ C}
                {g i : A ⇒ B} →
                ---------------
                f ≈ h →
                g ≈ i →
                -------------
                f ∘ g ≈ h ∘ i

  ------------
  -- private
  --   variable
  --     A B C D : Category
  --     f f′ : A ⇒ B
  --     g g′ : B ⇒ C
  --     h : C ⇒ D
  -- field
  --   assoc     : (h ∘  g) ∘ f  ≈  h ∘ (g  ∘ f)
  --   sym-assoc : h ∘ (g  ∘ f) ≈ (h ∘  g) ∘ f
  --   identityˡ : id ∘ f  ≈ f
  --   identityʳ : f ∘ id ≈ f
  --   ∘-resp-≈  : f ≈ f′ → g ≈ g′ → f ∘ g ≈ f′ ∘ g′

  op : Category
  Obj       op = Obj
  _⇒_       op = flip _⇒_
  _≈_       op = _≈_
  id        op = id
  _∘_       op = flip _∘_
  assoc     op = sym-assoc
  sym-assoc op = assoc
  identityˡ op = identityʳ
  identityʳ op = identityˡ
  ∘-resp-≈  op = flip ∘-resp-≈

  -- op =
  --   record
  --     { Obj       = Obj
  --     ; _⇒_       = flip _⇒_
  --     ; _≈_       = _≈_
  --     ; id        = id
  --     ; _∘_       = flip _∘_
  --     ; assoc     = sym-assoc
  --     ; sym-assoc = assoc
  --     ; identityˡ = identityʳ
  --     ; identityʳ = identityˡ
  --     ; ∘-resp-≈  = flip ∘-resp-≈
  --     }

open Category

module Helpers where
    _[_,_] : (C : Category {o} {ℓ} {e})
             (X : Category.Obj C)
             (Y : Category.Obj C)
             → Set ℓ
    _[_,_] = Category._⇒_

    _[_≈_] : (C : Category {o} {ℓ} {e})
             → ∀ {X Y}
             (f g : C [ X , Y ])
             → Set e
    _[_≈_] = Category._≈_

    _[_∘_] : (C : Category {o} {ℓ} {e})
             → ∀ {X Y Z}
             (f : C [ Y , Z ])
             (g : C [ X , Y ])
             → C [ X , Z ]
    _[_∘_] = Category._∘_

    -- sym-assoc (ℂ ᵒᵖ) -- works
    -- sym-assoc (ℂ ̂ᵒᵖ) -- broken

    _ᵒᵖ : Category {o} {ℓ} {e} → Category {o} {ℓ} {e}
    _ᵒᵖ = Category.op
    -- Obj       (ℂ ᵒᵖ) = Obj ℂ
    -- _⇒_       (ℂ ᵒᵖ) = flip (_⇒_ ℂ)
    -- _≈_       (ℂ ᵒᵖ) = _≈_ ℂ
    -- id        (ℂ ᵒᵖ) = id ℂ
    -- _∘_       (ℂ ᵒᵖ) = flip (_∘_ ℂ)
    -- assoc     (ℂ ᵒᵖ) = sym-assoc ℂ
    -- sym-assoc (ℂ ᵒᵖ) = assoc ℂ
    -- identityˡ (ℂ ᵒᵖ) = identityʳ ℂ
    -- identityʳ (ℂ ᵒᵖ) = identityˡ ℂ
    -- ∘-resp-≈  (ℂ ᵒᵖ) = flip (∘-resp-≈ ℂ)
    -- ℂ ᵒᵖ =
    --   record
    --     { Obj       = Obj ℂ
    --     ; _⇒_       = flip (_⇒_ ℂ)
    --     ; _≈_       = _≈_ ℂ
    --     ; id        = id ℂ
    --     ; _∘_       = flip (_∘_ ℂ)
    --     ; assoc     = sym-assoc ℂ
    --     ; sym-assoc = assoc ℂ
    --     ; identityˡ = identityʳ ℂ
    --     ; identityʳ = identityˡ ℂ
    --     ; ∘-resp-≈  = flip (∘-resp-≈ ℂ)
    --     }

open Helpers public

HASK : Category
HASK =
  record
    { Obj       = Set
    ; _⇒_       = λ A B → (A → B)
    ; _≈_       = _≡_
    ; id        = idₐ
    ; _∘_       = _∘ₐ_
    ; assoc     = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; ∘-resp-≈  = λ { refl refl → refl }
        -- λ {
        --   {A} {B} {C}
        --   {f} {h}
        --   {g} {i}
        --   (refl {f≡h})
        --   (refl {g≡i})
        --   →
        --     refl
        -- }
    }
