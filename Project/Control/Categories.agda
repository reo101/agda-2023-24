module Project.Control.Categories where

open import Level using (Level; zero; suc; _⊔_)

private
  variable
    o ℓ e : Level

open import Project.Relations using (EquivalenceRelation)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Lib.Utils using (flip) renaming (_∘_ to _∘ₐ_; id to idₐ)

-- <https://www.cas.mcmaster.ca/~carette/publications/2005.07059.pdf>

record Category : Set (suc (o ⊔ ℓ ⊔ e)) where
  eta-equality

  infix  4 _⇒_
  infix  4 _≈_
  infixr 9 _∘_

  field
    Obj : Set o
    _⇒_ : (A B : Obj) → Set ℓ
    _≈_ : ∀ {A B} → (f g : A ⇒ B) → Set e

    id  : ∀ {A} → (A ⇒ A)
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  ------------
  --- LAWS ---
  ------------
  field
    ≈-equiv   : ∀ {A B} →
                ---------
                EquivalenceRelation {ℓ} {e} {A ⇒ B} _≈_

    assoc     : ∀ {A B C D}
                {f : A ⇒ B}
                {g : B ⇒ C}
                {h : C ⇒ D} →
                -----------------------------
                (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

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

  op : Category
  Obj       op = Obj
  _⇒_       op = flip _⇒_
  _≈_       op = _≈_
  id        op = id
  _∘_       op = flip _∘_
  -- ≈-equiv   op = λ {A} {B} → ≈-equiv {B} {A}
  ≈-equiv   op = ≈-equiv
  assoc     op = symmetric assoc
    where open EquivalenceRelation ≈-equiv using (symmetric)
  identityˡ op = identityʳ
  identityʳ op = identityˡ
  ∘-resp-≈  op = flip ∘-resp-≈

open Category

module Helpers where
    _[_,_] : (C : Category {o} {ℓ} {e})
             (X : Category.Obj C)
             (Y : Category.Obj C) →
             Set ℓ
    _[_,_] = Category._⇒_

    _[_≈_] : (C : Category {o} {ℓ} {e}) →
             ∀ {X Y}
             (f g : C [ X , Y ]) →
             Set e
    _[_≈_] = Category._≈_

    _[_∘_] : (C : Category {o} {ℓ} {e}) →
             ∀ {X Y Z}
             (f : C [ Y , Z ])
             (g : C [ X , Y ]) →
             C [ X , Z ]
    _[_∘_] = Category._∘_

    _ᵒᵖ : Category {o} {ℓ} {e} → Category {o} {ℓ} {e}
    _ᵒᵖ = Category.op

    infixl 20 _ᵒᵖ

open Helpers public

HASK : Category
HASK =
  record
    { Obj       = Set
    ; _⇒_       = λ A B → (A → B)
    ; _≈_       = _≡_
    ; id        = idₐ
    ; _∘_       = _∘ₐ_
    ; ≈-equiv   = record { reflexive  = refl
                         ; symmetric  = sym
                         ; transitive = trans
                         }
    ; assoc     = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; ∘-resp-≈  = λ { refl refl → refl }
    }

-- private
--   op-involutive :
--     {C : Category {o} {ℓ} {e}} →
--     C ᵒᵖ ᵒᵖ ≡ C
--   op-involutive = refl
