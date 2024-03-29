module Project.Data.Reader where

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

Reader : Set → Set → Set
Reader A B = A → B

readerFunctor : (A : Set) → HomFunctor HASK
readerFunctor A = record
  { F[_] = Reader A
  ; fmap = λ f r → λ x → f (r x)
  ; identity =
      funext (λ { r → refl })
  ; homomorphism =
      funext (λ { r → refl })
  ; F-resp-≈ = λ {X} {Y} {f} {g} C[f≈g] → funext (λ { r →
      funext (λ { x →
        begin
          f (r x)
        ∼⟨ cong-app C[f≈g] (r x) ⟩
          g (r x)
        ∎
      })
    })
  }

readerMonad : (A : Set) → Monad HASK
readerMonad A = record
  { F = readerFunctor A
  ; η = record
    { component = λ { B → λ { x → λ _ → x
                            } }
    ; commutativity = refl
    }
  ; μ = record
    { component = λ { B → λ { r → λ x → r x x
                            } }
    ; commutativity = funext (λ { r →
        funext (λ { x → refl })
      })
    }
  ; μμ-associative = λ { {X} → refl}
  ; μη-associative = λ { {X} → refl}
  ; μη-identity = λ { {X} → refl}
  }
