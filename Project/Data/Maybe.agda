module Project.Data.Maybe where

open import Level using (Level; zero; suc; _⊔_)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Control.Categories using (Category; _[_,_]; _[_≈_]; _[_∘_]; HASK)
open import Project.Control.Functor using (Functor; HomFunctor; _[_]; _[fmap_])
open import Project.Control.Monad using (Monad)
open import Project.EquationalReasoning as EquationalReasoning
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
                    ∼⟨ cong just (cong-app C[f≈g] x) ⟩
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
  ; μμ-associative = λ { {X} → funext (λ
    { (just (just x)) ->
        begin
          x
        ∼⟨⟩
          x
        ∎
    ; (just nothing) ->
        begin
          nothing
        ∼⟨⟩
          nothing
        ∎
    ; nothing ->
        begin
          nothing
        ∼⟨⟩
          nothing
        ∎
    }) }
  ; μη-associative = λ { {X} → funext (λ
    { (just x) ->
        begin
          just x
        ∼⟨⟩
          just x
        ∎
    ; nothing ->
        begin
          nothing
        ∼⟨⟩
          nothing
        ∎
    }) }
  ; μη-identity = λ { {X} → funext (λ
    { (just x) ->
        begin
          just x
        ∼⟨⟩
          just x
        ∎
    ; nothing ->
        begin
          nothing
        ∼⟨⟩
          nothing
        ∎
    }) }
  }
