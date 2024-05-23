module Joro.TenLive where

open import Lib.Zero using (𝟘; zero-elim; ¬_)
open import Lib.One using (𝟙; ⟨⟩)
open import Lib.Two using (𝟚; tt; ff)
open import Lib.Nat using (ℕ; zero; suc; ozero; osuc; _≤_; ≤-suc; ≤-trans; +-right-suc) renaming (_<_ to Lt)
open import Lib.Fin using (Fin; zero; suc; natToFin)
open import Lib.Number using (Number; fromNat; Numℕ; NumFin)
open import Lib.Sum using (_+_; inl; inr)
open import Lib.Sigma using (Σ; _*_) renaming (_,_ to _,σ_)
open import Lib.Decidable using (Dec; no; yes)
open import Lib.List using (List; []; _∷_; length)
open import Lib.Vec using (Vec; HetVec; []; _∷_; congₙ)
open import Lib.Utils using (id)
open import Project.Data.Pair using (Pair; fst; snd) renaming (_,_ to _,,_)
open import Project.Data.Maybe using (Maybe; just; nothing)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)


open import Joro.NineLive

-- TODO:
-- We have some unit tests for applySubst in this file

-- TODO
-- buggy _[_], delete it


-- N (θ ∷ [])
-- ` 0 (0 ⇒ M ∷ [])
-- M

-- (λ N) M
-- app (lam N) M ??
-- N (`0 ⇒ M ∷ [])
-- app (lam (` 0)) (` 1) =β>
-- (` 1)
--
-- (λ0) 1 =β>
-- 1
-- (λx. x) y =β>
-- y

-- TODO definitions
-- "term" - Λ Γ τ
-- "closed term" - a term with no free variables
-- "beta reduction" - evaluating an expression
-- "beta redex" - a term we can reduce using beta reduction
-- "value" - functions, since we're in a pure lambda calculus. If we added e.g. chars/strings/nats to our language, those would be values as well

Closed : Type → Set
Closed τ = Λ [] τ

-- 3 5 6
-- 3 → 3
-- "asdf"
-- "asdf" → "asdf"
-- \x → x

-- \x → x ⇒ \x → x



-- TASK
-- A substitution that "performs one computation"
--
-- The idea here is that we'll encounter a situation like this one:
-- (λ N) M
-- translated to our syntax:
-- app (lam N) M
--
-- We have an application of a lambda function to another term, which
-- is the point at which we want to do a substitution, replacing all
-- variables occurences of the variable bound by the lambda with M.
--
-- We already have the function to do substitution (applySubst), so we only need
-- to build the appropriate applySubst(itution) now.
--
-- Thankfully this is easy to do:
-- "Coincidentally", the lambda has just introduced a variable for us to use
-- with the M we have, and the types line up, because of how we made the lam and app constructors.
--
-- Note that we also need to shift down all our other free variables, which we're not currently substituting,
-- as we just got rid of a single lambda.
reduceSubst :
  {Γ : Context} {τ : Type} →
  Λ Γ τ →
  (τ ∷ Γ ↦ Γ)
reduceSubst l Z = l
reduceSubst l (S p) = var p

-- NOTE
-- A convenient synonym for substituting by reduceSubst
-- You can also make a non-operator version if you prefer to not have "operator soup"
_[0⇒_] :
  {Γ : Context} {τ π : Type} →
  Λ (π ∷ Γ) τ →
  Λ Γ π →
  Λ Γ τ
x [0⇒ t ] = applySubst (reduceSubst t) x

infix 15 _[0⇒_]

-- NOTE
-- Some unit tests for your substitution and reduceSubst

_ :
  withContext (base 42 ∷ base 69 ∷ [])
    (` 0 [0⇒ ` 1 ])
  ≡
  (` 1)
_ = refl

_ :
  withContext (base 42 ∷ base 1337 ∷ [])
    (
      (lam {_} {base 69} (` 0))
        [0⇒
          ` 1
        ]
    )
  ≡
  lam (` 0)
_ = refl

foo0 : Λ (base 0 ⇒ base 0 ∷ []) (base 0 ⇒ base 0)
foo0 = lam (app (` 1) (app (` 1) (` 0)))

foo1 : Λ [] (base 0 ⇒ base 0)
foo1 = lam (` 0)

foo2 : Λ [] (base 0 ⇒ base 0)
foo2 = lam (app (lam (` 0)) (app (lam (` 0)) (` 0)))

_ : foo0 [0⇒ foo1 ] ≡ foo2
_ = refl

-- TASK
-- We want Val to be a predicate stating that a certain term is a Value.
--
-- We're working in a "pure" lambda calculus, meaning we only have variables, application, and lambdas.
--
-- In such a lambda calculus, the only fully closed terms are lambdas, so we need to have a single constructor here,
-- to expressing the fact that lam N is a value.
-- Val N = "доказателство че N е стойност"
data Val : {Γ : Context} {τ : Type} → Λ Γ τ → Set where
  v-lam : {τ σ : Type}
          (l : Λ (σ ∷ []) τ) →
          Val {[]} {σ ⇒ τ} (lam l)

-- TASK
-- N =β> M is going to express the relation that N beta reduces to M.
-- You're going to define this relation by following the description I've given below for what we want to achieve.
--
-- We're going to have three rules/constructors here:
-- 1. red-beta
--
-- First, we clearly need to have a rule (the beta rule) that states "If you have (λN) M, you can reduce that to N [0⇒ M ]", as that's how our substitution works.
-- Furthermore, we'll restrict ourselves to only applying this rule when M is a value, to force us to first reduce our arguments before calling a function (strict/call by value semantics)
-- Taking all that into account, we need to add a constructor that states
-- If M is a value, then app (lam N) M reduces to N [0⇒ M ]
--
-- Apart from that, we'll also need two other rules, to allow reduction to "see past" applications.
--
-- 2. red-app-l
-- Imagine you have the following scenario
--
-- ((λ0) (λ0)) (λ0)
--
-- i.e.
-- app
--  (app
--    (lam (` 0))
--    (lam (` 0))
--  )
--  (lam (` 0))
-- Notice that in the left argument of the outermost app, there's a beta redex waiting to be evaluated, that being (λ0) (λ0)
--
-- However, if we only allow reducing terms of the form ((λN) M), we can't actually do that reduction, because
-- there's nothing us do an "inner" reduction first, i.e. one that is hidden behind an app.
--
-- In order to allow reduction to proceed in such a case, we need to add a constructor which states that
-- If we can reduce N to N', then we can also reduce app N M to app N' M
--
-- By using this constructor, we can now first do a reduction on the left of our application
--
-- 3. red-app-r
-- Mirroring 2. we can also imagine having the following scenario
-- (λ0) ((λ0) (λ0))
--
-- So by the same logic, we'll need a constructor to "see past" the right argument of an app.
--
-- We'll do something cheesy here, which is to restrict ourselves to only applying this to values.
-- We do this so that we always have only a single way we could proceed with reduction, which simplifies our proofs later.
--
-- So our third constructor should state the following:
-- If N is a value, and we can reduce M to M', then we can reduce app V M to app V M'
--
-- Note that if we instead drop the "If N is a value" part, we can then choose to apply either red-app-l or red-app-r in some terms, e.g. in
-- ((λ0) (λ0)) ((λ0) (λ0))
--
-- TODO drop constructors
data _=β>_ {Γ : Context} {τ : Type} : Λ Γ τ → Λ Γ τ → Set where
  red-β     : {σ : Type} {M : Λ (σ ∷ Γ) τ} {N : Λ Γ σ} → Val N → app (lam M) N =β> M [0⇒ N ]
  red-app-l : {σ : Type} {M₁ M₂ : Λ Γ (σ ⇒ τ)} {N : Λ Γ σ} → M₁ =β> M₂ → app M₁ N =β> app M₂ N
  red-app-r : {σ : Type} {M : Λ Γ (σ ⇒ τ)} {N₁ N₂ : Λ Γ σ} → Val M → N₁ =β> N₂ → app M N₁ =β> app M N₂

infix 2 _=β>_

-- TASK
-- In order to do chains of beta reductions, we'll need to make a reflexive and transitive version of _=β>*
--
-- Add two constructors:
-- 1. Any term reduces to itself (reflexivity)
-- 2. If N =β> M and M =β>* L, then N =β>* L (transitivity)
data _=β>*_ {Γ : Context} {τ : Type} : Λ Γ τ → Λ Γ τ → Set where
  =β>*-refl : {l : Λ Γ τ} → l =β>* l
  =β>*-cons : {l₁ l₂ l₃ : Λ Γ τ} → l₁ =β> l₂ → l₂ =β>* l₃ → l₁ =β>* l₃

infix 2 _=β>*_

-- NOTE
-- We'll now introduce the same utilities we used for equational reasoning, but for =β>* instead,
-- so that we can write proofs using them

-- TASK
-- Synonym for reflexivity, used to end our proofs, much like we used _QED
_β∎ : {Γ : Context} {τ : Type} (N : Λ Γ τ) → N =β>* N
N β∎ = =β>*-refl

infix 3 _β∎

{-# DISPLAY =β>*-refl {l = N} = N β∎ #-}

-- TASK
-- Synonym for transitvity, to allow us to chain proofs, much like we used _=[_]_
_⇒⟨_⟩_ :
  {Γ : Context} {τ : Type} →
  {M L : Λ Γ τ} →
  (N : Λ Γ τ) →
  N =β> M →
  M =β>* L →
  N =β>* L
N ⇒⟨ p ⟩ q = =β>*-cons p q

infixr 2 _⇒⟨_⟩_

{-# DISPLAY =β>*-cons {l₁ = N} p q = N ⇒⟨ p ⟩ q #-}

_⇒⟨⟩_ :
  {Γ : Context} {τ : Type} →
  {N : Λ Γ τ} →
  (M : Λ Γ τ) →
  M =β>* N →
  M =β>* N
M ⇒⟨⟩ q = q

infixr 2 _⇒⟨⟩_

-- TASK
-- write
-- (λ0)
-- as a Λ
idΛ : {Γ : Context} {τ : Type} → Λ Γ (τ ⇒ τ)
idΛ = lam (` 0)

module Ex1 where

  -- TASK
  -- Write
  -- ((λ0) (λ0)) (λ0)
  -- as a Λ
  ex1 : Λ [] (α ⇒ α)
  ex1 = app (app idΛ idΛ) idΛ

  -- TASK
  -- Prove that ex1 reduces to idΛ
  _ : ex1 =β>* idΛ
  _ =
      ex1
    ⇒⟨⟩
      app (app idΛ idΛ) idΛ
    ⇒⟨ red-app-l (red-β (v-lam (` 0))) ⟩
      app idΛ idΛ
    ⇒⟨ red-β (v-lam (` 0)) ⟩
      idΛ
    β∎

module Ex2 where

  -- TASK
  -- Write
  -- (λ0) ((λ0) (λ0))
  -- as a Λ
  ex2 : Λ [] (α ⇒ α)
  ex2 = app idΛ (app idΛ idΛ)

  -- TASK
  -- Prove that ex1 reduces to idΛ
  _ : ex2 =β>* idΛ
  _ =
      ex2
    ⇒⟨⟩
      app idΛ (app idΛ idΛ)
    ⇒⟨ red-app-r (v-lam (` 0)) (red-β (v-lam (` 0))) ⟩
      app idΛ idΛ
    ⇒⟨ red-β (v-lam (` 0)) ⟩
      idΛ
    β∎

module Ex3 where
  ex3 : ¬ (Λ [] ((α ⇒ α) ⇒ α))
  ex3 (app M N) = {! !}
  ex3 (lam M) = {! !}

-- TASK
-- Formulate and prove that if a term is a value, then it cannot reduce.
Val-no-red : {Γ : Context} {τ : Type} {M N : Λ Γ τ} → Val M → ¬ (M =β> N)
Val-no-red (v-lam l) ()

-- TASK
-- Formulate and prove that if a term can reduce, then it is not a value
no-red-Val : {Γ : Context} {τ : Type} {M N : Λ Γ τ} → M =β> N → ¬ (Val M)
no-red-Val () (v-lam l)

-- TASK
-- We'll want to formulate, prove, and use the following property:
-- "Progress properτ": If a term is closed, then it is either a Val, or it can make a reduction step.
--
-- Implement a data type which captures these two possibilities for a given term N.
data Progress {τ : Type} (N : Λ [] τ) : Set where
  progress-val : Val N → Progress N
  progress-step : (M : Λ [] τ) → N =β> M → Progress M → Progress N

-- TASK
-- Prove the progress property, as stated above.
{-# TERMINATING #-}
progress : {τ : Type} → (N : Λ [] τ) → Progress N
progress (app M N) with progress M
... | progress-step  M′ M=β>M′ pm =
  progress-step (app M′ N) (red-app-l M=β>M′) (progress (app M′ N))
... | progress-val (v-lam M′) with progress N
...                                 | progress-val (v-lam N′) =
  progress-step (M′ [0⇒ lam N′ ]) (red-β (v-lam N′)) (progress (M′ [0⇒ lam N′ ]))
...                                 | progress-step N′ N=β>N′ pn =
  progress-step (app M N′) (red-app-r (v-lam M′) N=β>N′) (progress (app M N′))
progress (lam N) = progress-val (v-lam N)

-- TASK
-- Implement a function which determines if a given term is a value by using progress.
decVal : {τ : Type} → (N : Λ [] τ) → Dec (Val N)
decVal (app M N) = no (λ ())
decVal (lam N) = yes (v-lam N)

-- data Maybe (A : Set) : Set where
--   no : Maybe A
--   yes : A → Maybe A

-- NOTE
-- For any closed term, we know that it reduces to some M, which is also a Val.
-- This data type captures this properτ.
--
-- We use a Maybe (Val M) due to some termination issues described below in eval
data Steps {τ : Type} : Λ [] τ → Set where
  steps :
    {N : Λ [] τ} →
    (M : Λ [] τ) →
    N =β>* M →
    Val M →
    Steps N

-- TASK
-- Implement an evaluator for closed lambda terms.
-- We take an extra Nat argument as a counter for how many reduction steps we're allowed to do.
--
-- Theoretically, we don't need to count steps, because we usually know that closed STLC terms
-- can always be evaluated to values, but I didn't have the time to figure out how to satisfy
-- Agda's termination checker, so instead we use this Nat to be the decreasing value for each
-- recursive call, guaranteeing that we won't loop forever and making Agda happy.
{-# TERMINATING #-}
eval : {τ : Type} → (N : Λ [] τ) → Steps N
eval N with progress N
... | progress-val (v-lam l) = steps N =β>*-refl (v-lam l)
... | progress-step M N=β>M pm with eval M
... | steps M′ M=β>*M′ (v-lam l) = steps M′ (=β>*-cons N=β>M M=β>*M′) (v-lam l)
