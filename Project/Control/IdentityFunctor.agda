{-# OPTIONS --allow-unsolved-metas #-}

module Project.Control.IdentityFunctor where

open import Level using (Level; zero; suc; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Lib.Utils using (id)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_])
open import Project.Relations using (EquivalenceRelation)
open import Project.Postulates using (funext)

private
  variable
    o ℓ e : Level

-- TODO:
-- BUG: cannot seem to prove the laws (agda moment)
--
-- Id : {ℂ : Category {o} {ℓ} {e}} → HomFunctor ℂ
-- Id {ℂ = ℂ} = record
--   { F[_] = id
--   ; fmap = id
--   -- ; identity = reflexive {Category.id ℂ}
--   ; identity = λ { {X} → ? }
--   ; homomorphism = {! !}
--   ; F-resp-≈ = {! !}
--   }
--   where open EquivalenceRelation (Category.≈-equiv ℂ) using (reflexive)
--   -- where open Category ℂ hiding (id) -- using (≈-equiv)
--   --       open EquivalenceRelation ≈-equiv using (reflexive)

IdHASK : HomFunctor HASK
IdHASK = record
  { F[_] = id
  ; fmap = id
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = id
  }

Id : (ℂ : Category {o} {ℓ} {e}) → HomFunctor ℂ
-- Id .HASK = IdHASK
Id _ = ?

