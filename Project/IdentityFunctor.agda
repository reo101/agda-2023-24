{-# OPTIONS --allow-unsolved-metas #-}

module Project.IdentityFunctor where

open import Level using (Level; zero; suc; _⊔_)

open import Lib.Equality using (_≡_; refl)
open import Lib.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎; sym; cong; cong-app; trans; subst)
open import Lib.Utils using (id)

open import Project.Relations using (EquivalenceRelation)
open import Project.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Functor using (Functor; HomFunctor; _[_]; _[fmap_])
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

