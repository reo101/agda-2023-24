module Project.Data.Pair where

open import Level using (Level; zero; suc; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_])
open import Project.Control.Monad using (Monad)
open import Project.Postulates using (funext)

record Pair (A B : Set) : Set where
  eta-equality
  constructor _,_
  field
    fst : A
    snd : B
open Pair public using (fst; snd)

pairFunctor : (A : Set) → HomFunctor HASK
pairFunctor A = record
  { F[_] = Pair A
  ; fmap = λ f (a , b) → a , f b
  ; identity =
      funext (λ { (a , b) → refl })
  ; homomorphism =
      funext (λ { (a , b) → refl })
  ; F-resp-≈ = λ {X} {Y} {f} {g} C[f≈g] →
      funext (λ { (a , b) →
                    begin
                      (a , f b)
                    ∼⟨ cong (a ,_) (cong-app C[f≈g] b) ⟩
                      (a , g b)
                    ∎
                })
  }

-- -- NOTE: only when A is a Monoid
-- --
-- pairMonad : (A : Set) → Monad HASK
-- pairMonad A = record
--   { F = pairFunctor A
--   ; η = record
--     { component = λ { B → λ { b → ? , b
--                             } }
--     ; commutativity = refl
--     }
--   ; μ = record
--     { component = λ { B → λ { (a₁ , (a₂ , b)) → (? a₁ a₂) , b
--                             } }
--     ; commutativity = funext (λ { (a , b) → refl
--                                 })
--     }
--   ; μμ-associative = ?
--   ; μη-associative = ?
--   ; μη-identity = ?
--   }
