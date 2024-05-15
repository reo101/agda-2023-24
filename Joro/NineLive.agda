{-# OPTIONS --inversion-max-depth=5000 #-}

module Joro.NineLive where

open import Lib.Zero using (𝟘; zero-elim)
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
open import Project.Data.Pair using (Pair; _,_; fst; snd)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

-- TODO: Lib.ℕ has Lt
-- TODO: Lib.SnocList

-- α β γ δ ...
-- 0 1 2 3 4
-- x_0, x_1
data Type : Set where
  base : ℕ → Type
  _⇒_ : Type → Type → Type

_≣ℕ≣_ : ℕ → ℕ → Set
zero ≣ℕ≣ zero = 𝟙
zero ≣ℕ≣ suc y = 𝟘
suc x ≣ℕ≣ zero = 𝟘
suc x ≣ℕ≣ suc y = x ≣ℕ≣ y

≣ℕ≣⇒≡ : {n₁ n₂ : ℕ} → n₁ ≣ℕ≣ n₂ → n₁ ≡ n₂
≣ℕ≣⇒≡ {zero} {zero} p = refl
≣ℕ≣⇒≡ {suc n₁} {suc n₂} p = cong suc (≣ℕ≣⇒≡ p)

_≣T≣_ : Type → Type → Set
base n₁ ≣T≣ base n₂ = n₁ ≣ℕ≣ n₂
base x ≣T≣ (τ₂ ⇒ τ₃) = 𝟘
(τ₁ ⇒ τ₂) ≣T≣ base x = 𝟘
(τ₁ ⇒ τ₂) ≣T≣ (τ₃ ⇒ τ₄) = Pair (τ₁ ≣T≣ τ₃) (τ₂ ≣T≣ τ₄)

≣T≣⇒≡ : {τ₁ τ₂ : Type} → τ₁ ≣T≣ τ₂ → τ₁ ≡ τ₂
≣T≣⇒≡ {base n₁} {base n₂} p = cong base (≣ℕ≣⇒≡ p)
≣T≣⇒≡ {τ₁ ⇒ τ₂} {τ₃ ⇒ τ₄} (τ₁≣T≣τ₃ , τ₂≣T≣τ₄) =
  begin
    τ₁ ⇒ τ₂
  ∼⟨ cong (τ₁ ⇒_) (≣T≣⇒≡ τ₂≣T≣τ₄) ⟩
    τ₁ ⇒ τ₄
  ∼⟨ cong (_⇒ τ₄) (≣T≣⇒≡ τ₁≣T≣τ₃) ⟩
    τ₃ ⇒ τ₄
  ∎
--   with ≣T≣⇒≡ τ₁≣T≣τ₃ | ≣T≣⇒≡ τ₂≣T≣τ₄
-- ... | refl | refl = refl

α : Type
α = base 0

β : Type
β = base 1

γ : Type
γ = base 2

δ : Type
δ = base 3

infixr 11 _⇒_

-- λx.λy.x
-- const :: a → b → a
-- const x y = x

_ : Type
_ = α ⇒ β ⇒ α

Context : Set
Context = List Type

-- α,β,γ
_ : Context
_ = α ∷ β ∷ γ ∷ []

-- n
-- Γ := τ(n-1),....τ0
-- Lambda
-- i : α, α ∈ Γ



-- data _In_ {A : Set} : A → List A → Set where
--   here : {x : A} {xs : List A} → x In (x ∷ xs)
--   there : {x y : A} {xs : List A} → x In xs → x In (y ∷ xs)
--
-- _ : 3 In (3 ∷ 4 ∷ 5 ∷ [])
-- _ = here {ℕ} {3} {4 ∷ 5 ∷ []}
--
-- _ : 3 In (3 ∷ 4 ∷ 3 ∷ [])
-- _ = here
--
-- _ : 3 In (3 ∷ 4 ∷ 3 ∷ [])
-- _ = there (there here)

data _In_ : Type → Context → Set where
  -- here
  Z : {ty : Type} {ctx : Context} → ty In (ty ∷ ctx)
  -- there
  S_ : {ty1 ty2 : Type} {ctx : Context} → ty1 In ctx → ty1 In (ty2 ∷ ctx)

infixr 12 S_

infix 10 _In_

Γ : Context
Γ = γ ∷ β ∷ α ∷ []

_ : α In Γ
_ = S S Z



-- TODO: In for lists
-- TODO: replacing debruijn indices by membership proofs
-- TODO: In for contexts

-- TODO: examples of In


-- TASK
-- Indexing a context with a number which is "in bounds" of the context
-- (i.e. the number used to index is less than the length of the context)
ix : (n : ℕ) (ctx : Context) → (Lt n (length ctx)) → Type
ix zero (x ∷ ctx) ⟨⟩ = x
ix (suc n) (x ∷ ctx) sucn<=lengthcxt = ix n ctx sucn<=lengthcxt

-- TASK
--
-- This is not only useful as a standalone statement,
-- but we're also going to use it to allow us to more conveniently
-- write ℕs instead of manually writing out variables for a lambda
-- term later on.
ixIn :
  -- for a given n
  (n : ℕ)
  -- and a context
  (ctx : Context)
  -- if we know that n is less than the length of the context
  (p : Lt n (length ctx)) →
  -- then we can not only fetch out the item at index n,
  -- but also get proof that it is In the context
  ix n ctx p In ctx
ixIn zero (x ∷ ctx) ⟨⟩ = Z
ixIn (suc n) (x ∷ ctx) p = S ixIn n ctx p

-- TASK
-- Use the lecture notes to guide you on implementing the data type for
-- simply typed nameless lambda terms.
--
-- Remember that we're using _In_ to express a typed debruijn index.
data Λ (Γ : Context) : Type → Set where
  var : {τ : Type} (p : τ In Γ) → Λ Γ τ
  app : {σ₁ σ₂ : Type}
        (M₁ : Λ Γ (σ₁ ⇒ σ₂))
        (M₂ : Λ Γ σ₁) →
        Λ Γ σ₂
  lam : {σ₁ σ₂ : Type}
        (M : Λ (σ₁ ∷ Γ) σ₂) →
        Λ Γ (σ₁ ⇒ σ₂)

-- TASK
-- Write a term which is a single variable
_ : Λ (α ∷ []) α
_ = var Z

-- TASK
-- Write a term which is a single variable, in a context of two possibly variables.
_ : Λ (γ ∷ α ∷ β ∷ []) α
_ = var (S Z)

-- TASK
-- Write the identity function term, i.e. λx.x
_ : Λ [] (α ⇒ α)
_ = lam (var Z)

-- TASK
-- Write the "const" function, i.e. λx.λy.x
_ : Λ [] (α ⇒ β ⇒ α)
_ = lam (lam (var (S Z)))

-- TASK
-- Write the "s combinator", i.e. λf.λg.λx.f x (g x)
_ : Λ [] ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
_ = lam (lam (lam (app (app (var (S S Z)) (var Z))
                       (app (var (S Z))   (var Z)))))

-- TASK
-- This function will allow us to refer to variables by their "debruin indices",
-- by implicitly converting numbers to In proofs (via ixIn), and then injecting them as vars.
`_ : {ctx : Context} (n : ℕ) {p : Lt n (length ctx)} → Λ ctx (ix n ctx p)
`_ {ctx} n {p} = var (ixIn n ctx p)

instance
  NumIn : ∀ {τ Γ} → Number (τ In Γ)
  Number.Constraint (NumIn {τ} {Γ}) k = Σ (Lt k (length Γ)) λ k<#Γ → ix k Γ k<#Γ ≣T≣ τ
  Number.fromNat (NumIn {τ} {Γ}) k {{k<#Γ ,σ τ✓}}
    with ≣T≣⇒≡ {τ₁ = ix k Γ k<#Γ} {τ₂ = τ} τ✓
    -- with τ✓
  ... | refl = ixIn k Γ k<#Γ

_ : Σ (Lt 0 (length (base 0 ∷ []))) λ k<#Γ → ix 0 (base 0 ∷ []) k<#Γ ≣T≣ base 0
_ = _

-- TASK
-- Repeat the examples from above, but with `_

-- TASK
-- Write a term which is a single variable
-- _ : Λ (α ∷ []) α
-- _ = var (fromNat 0 {{⟨⟩ , refl}})

-- fromNat′ : {A : Set} {num : Number A} (n : ℕ) {c : Number.Constraint num n} → A
-- fromNat′ {A} {num} n {c} = fromNat {A = A} {{r = num}} n {{c}}

instance
  -- mqu : (α In α ∷ [])
  -- mqu = NumIn {τ = α} {Γ = α ∷ []}
  -- mqu : ∀ {τ Γ k} → {k<#Γ : Lt k (length Γ)} → ix k Γ k<#Γ ≡ τ
  -- mqu {τ} {τ′ ∷ Γ} {zero} {⟨⟩} =
  --   begin
  --     τ′
  --   ∼⟨ ? ⟩
  --     τ
  --   ∎
  -- mqu {τ} {τ′ ∷ Γ} {suc k} {k<#Γ} = {! !}

_ : α In (α ∷ [])
_ = fromNat 0 {{⟨⟩ ,σ ⟨⟩}}
-- _ = fromNat 0 {{⟨⟩ ,σ refl}}
-- _ = fromNat 0 {{r = NumIn {τ = α} {Γ = α ∷ []}}}

-- TASK
-- Write a term which is a single variable, in a context of two possibly variables.
_ : Λ (γ ∷ α ∷ β ∷ []) α
_ = ` 1
-- _ = var (S Z)

-- TASK
-- Write the identity function term, i.e. λx.x
_ : Λ [] (α ⇒ α)
_ = lam (var Z)

-- TASK
-- Write the "const" function, i.e. λx.λy.x
_ : Λ [] (α ⇒ β ⇒ α)
_ = lam (lam (var (S Z)))

-- TASK
-- Write the "s combinator", i.e. λf.λg.λx.f x (g x)
_ : Λ [] ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
_ = lam (lam (lam (app (app (var (S S Z)) (var Z))
                       (app (var (S Z))   (var Z)))))
{-
-- NOTE
-- A renaming is a way for us to send any type in one context to another context.
--
-- Since our variables are membership proofs(In), this means that we're
-- effectively renaming each variable, hence the name of this type synonym.
Ren : Context → Context → Set
Ren γ δ = {τ : Type} → τ In γ → τ In δ

-- TASK
-- The identity renaming, does nothing.
idRename : {γ : Context} → Ren γ γ
idRename = ?

-- TASK
-- A renaming that "shifts" all the variables "up by one".
shift1Rename : {γ : Context} {sigma : Type} → Ren γ (γ ∷ sigma)
shift1Rename = ?

-- TASK
-- We can "extend" renamings
-- In other words, if we can rename n variables, we can also rename n+1 variables,
-- by not doing anything to the freshly introduced new variable (sigma)
--
-- We need this because when we're doing a renaming of a term and want to recurse under a lambda,
-- the lambda will introduce a new variable, while our renaming (up to that point) will
-- only deal with the existing variables, before the newly introduced one.
--
-- Note that we do indeed *want* to not rename the newly introduced variable, because
-- when we apply this for lambdas, the newly introduced variable will be a *bound* variable,
-- and we want our renaming to not affect it.
extRen :
  {sigma : Type} {γ δ : Context} →
  Ren γ δ →
  Ren (γ ∷ sigma) (δ ∷ sigma)
extRen = ?

-- TASK
-- Applying/lifting a renaming to a term
rename :
  {γ δ : Context} →
  -- if we have a renaming ρ
  Ren γ δ →
  -- and we have a typed term in the domain of that ρ
  {τ : Type} → Λ γ τ →
  -- then we can rename all the variables by using ρ while preserving the type of the term
  Λ δ τ
rename = ?

-- NOTE
-- tl;dr Again, as with untyped Lams, we need to explicitly specify what our context is
-- because a single term is valid in many contexts.
--
-- longer version:
-- This function helps us specify the free variables of a Lam,
-- because in our Λ definition, nothing is preventing us from adding as many free variables as we like.
-- For example, the term
-- var Z
-- is a valid term in
-- Λ (α ∷ []) α
-- but it is also a valid term in
-- Λ (β ∷ β ∷ β ∷ α ∷ []) α
-- Agda does not like this, since it can't figure out what the context should be,
-- so we need to manually specify it.
withContext : {τ : Type} (γ : Context) → Λ γ τ → Λ γ τ
withContext _ x = x

-- NOTE
-- Convenience synonyms for small contexts
pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []

-- for example
_ : Context
_ = [ base 1 ]

_ : Context
_ = [ base 2 , (base 1 ⇒ base 2) , base 1 ]

-- UNIT TESTS
-- Note that you might (unfortunately) also have to specify implicit args to internal lambdas here,
-- since if we write (var Z), it is, again, not clear which type we want this var Z to be
-- (it could be any base n, for whatever n you pick)
--
-- Our id renaming should do nothing
_ : withContext [ base 5 ] (rename idRename (` 0)) == ` 0
_ = refl

_ : withContext [] (rename idRename (lam {[]} {α} {α} (` 0))) == lam (` 0)
_ = refl

-- Our shift renaming should.. shift
_ :
  withContext [ base 42 , base 69 ]
    (rename shift1Rename
      (withContext [ base 42 ] (` 0)))
  ==
  ` 1
_ = refl

-- but it should take care not to touch bound variables
_ :
  withContext [ base 42 , base 69 ]
    (rename shift1Rename
      (withContext [ base 42 ]
        (app
          (lam {_} {base 42} (` 0))
          (` 0))))
  ==
  app (lam (` 0)) (` 1)
_ = refl

-- NOTE
-- Similarly to a Ren,
-- a substitution is a way to map all the variables in one context to terms in another context.
--
-- Since our variables are membership proofs(In), this means that we're
-- effectively substituting each variable for a term.
Subst : Context → Context → Set
Subst γ δ = {τ : Type} → τ In γ → Λ δ τ

-- TASK
-- The substitution that replaces all variables with themselves.
idSubst : {γ : Context} → Subst γ γ
idSubst = ?

-- TASK
-- Once again, as with renamings, we can "extend" substitutions
-- If we have a substitution for n variables, we can make a substitution for n+1 variables,
-- by not doing anything for the newly introduced variables.
--
-- Once again, this is useful when we encounter a lambda, and we need to somehow deal with
-- the newly introduced variable appropriatley.
--
-- Note that we do indeed *want* to not substitute the newly introduced variable, because
-- when we apply this for lambdas, the newly introduced variable will be a *bound* variable,
-- and we want our substitution to not affect it.
extSubst :
  {γ δ : Context} {sigma : Type} →
  Subst γ δ →
  Subst (γ ∷ sigma) (δ ∷ sigma)
extSubst = ?

-- TASK
-- We can apply/extend substitutions to terms
subst :
  {γ δ : Context} {τ : Type} →
  -- if we have a substitution θ
  Subst γ δ →
  -- and we have a typed term whose variables are all in the domain of θ
  Λ γ τ →
  -- then we can apply θ to get a new term of the same type
  Λ δ τ
subst = ?

-- NOTE
-- A "pretty" synonym for subst, somewhat mimicking some usual mathematical syntax
-- for applying substitutions.
_[_] :
  {γ δ : Context} {τ : Type} →
  Λ γ τ →
  Subst γ δ →
  Λ δ τ
x [ th ] = subst th x

infix 10 _[_]

-- UNIT TESTS
-- Write some unit tests yourselves :P
-}
