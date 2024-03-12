module Project.Data.Pair where

open import Level using (Level; zero; suc; _⊔_)

open import Lib.Equality using (_≡_; refl)
open import Lib.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎; sym; cong; cong-app; trans; subst)

open import Project.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Functor using (Functor; HomFunctor; _[_]; _[fmap_])
open import Project.Monad using (Monad)
open import Project.Postulates using (funext)

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open Pair

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
                    ≡⟨ cong (a ,_) (cong-app C[f≈g] b) ⟩
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
--   }
