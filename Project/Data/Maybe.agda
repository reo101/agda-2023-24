module Project.Data.Maybe where

open import Level using (Level; zero; suc; _⊔_)

open import Lib.Equality using (_≡_; refl)
open import Lib.≡-Reasoning using (begin_; step-≡; _≡⟨⟩_; _∎; sym; cong; cong-app; trans; subst)

open import Project.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Functor using (Functor; HomFunctor; _[_]; _[fmap_])
open import Project.Monad using (Monad)
open import Project.Postulates using (funext)

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
  ; F-resp-≈ = λ {X} {Y} {f} {g} C[f≈g] →
      funext (λ { nothing → refl
                ; (just x) →
                    begin
                      just (f x)
                    ≡⟨ cong just (cong-app C[f≈g] x) ⟩
                      just (g x)
                    ∎
                })
  }

maybeMonad : Monad HASK
maybeMonad = record
  { F = maybeFunctor
  ; η = record
    { component = λ { X → just }
    ; commutativity = refl
    }
  ; μ = record
    { component = λ { X → λ { (just x) → x
                            ; nothing → nothing
                            } }
    ; commutativity = funext (λ { (just x) → refl
                                ; nothing → refl
                                })
    }
  }
