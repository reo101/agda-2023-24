module Lib.Vec where

open import Lib.Nat using (ℕ; zero; suc; _+_)
open import Lib.Utils using (_∘_; id)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

import Level

infixr 20 _∷_

data Vec {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (1 + n)

map : ∀ {ℓ} {A B : Set ℓ} → ∀ {n} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- open import Lib.Tactics using (default)

data HetVec {ℓ₁ ℓ₂} {tf : Set ℓ₁ → Set ℓ₂} :
            {n : ℕ} (ts : Vec (Set ℓ₁) n)  →
            Set (Level.suc (ℓ₁ Level.⊔ ℓ₂)) where
  []  : HetVec []
  _∷_ : ∀ {n t ts}
        (x : tf t)
        (xs : HetVec {tf = tf} {n = n} ts) →
        HetVec {n = suc n} (t ∷ ts)

Nary : {n : ℕ} (ts : Vec Set n) (rt : Set) → Set
Nary [] rt = rt
Nary (t ∷ ts) rt = t → Nary ts rt

hetmap : ∀ {ℓ₁ ℓ₂ n ts tf₁ tf₂}
         (f : {t : Set ℓ₁} → tf₁ t → tf₂ t)
         (xs : HetVec {ℓ₁} {ℓ₂} {tf = tf₁} {n} ts) →
         HetVec {ℓ₁} {ℓ₂} {tf = tf₂} {n} ts
hetmap f [] = []
hetmap f (x ∷ xs) = f x ∷ hetmap f xs

hetliftmap : ∀ {ℓ₁ ℓ₂ n ts tf}
             (f : {t : Set ℓ₁} → tf t → Set ℓ₂)
             (xs : HetVec {ℓ₁} {ℓ₂} {tf = tf} {n = n} ts) →
             Vec (Set ℓ₂) n
hetliftmap f [] = []
hetliftmap f (x ∷ xs) = f x ∷ hetliftmap f xs

applyₙ : ∀ {n ts tf rt} →
         -- ∀ {n ts} → {@(tactic default id) tf : ?} → {rt} →
         (f : Nary {n = n} (map tf ts) rt) →
         (xs : HetVec {tf = tf} ts) →
         rt
applyₙ f []       = f
applyₙ f (x ∷ xs) = applyₙ (f x) xs

open import Project.Data.Pair using (Pair; _,_; fst; snd)

congₙ : {n : ℕ}
        {ts : Vec Set n}
        {rt : Set}
        (f : Nary (map id ts) rt)
        (argss : HetVec {tf = (λ t → Pair t t)} ts)
        (args≡s : HetVec {tf = id} (hetliftmap (λ {t} (t₁ , t₂) → t₁ ≡ t₂) argss)) →
        applyₙ f (hetmap fst argss) ≡ applyₙ f (hetmap snd argss)
congₙ f [] [] = refl
-- congₙ {ts = t ∷ ts} f ((arg₁ , arg₂) ∷ argss) (refl ∷ args≡s) = congₙ {ts = ts} (f arg₁) argss args≡s
congₙ f
      ((arg₁ , arg₂) ∷ argss)
      (args≡ ∷ args≡s)
      with args≡
... | refl = congₙ (f arg₁) argss args≡s

module _ where
  proba₁ : ℕ
  proba₁ = applyₙ {tf = id} _+_ (1 ∷ 2 ∷ [])

  proba₂ : HetVec {tf = id} (ℕ ∷ ℕ ∷ [])
  proba₂ = hetmap {tf₁ = λ t → Pair t t} fst (1 , 2 ∷ 2 , 3 ∷ [])

  proba₃ : 2 + 3 ≡ (1 + 1) + (1 + 1 + 1)
  proba₃ = congₙ _+_ ((2 , (1 + 1)) ∷ (3 , (1 + 1 + 1)) ∷ []) (refl ∷ refl ∷ [])

  data Kek : Set where
    nula : Kek
    1+_ : Kek → Kek

  _ : Kek
  _ = 1+ 1+ 1+ nula

