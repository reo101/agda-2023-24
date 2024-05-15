{-# OPTIONS --no-unicode #-}

module Joro.SevenLive where

open import Lib.Zero using (𝟘; zero-elim)
open import Lib.One using (𝟙; ⟨⟩)
open import Lib.Two using (𝟚; tt; ff)
open import Lib.Nat using (ℕ; zero; suc; ozero; osuc; _≤_; +-right-suc)
open import Lib.Sum using (_+_; inl; inr)
open import Lib.Sigma using (Σ; _,_; fst; snd; _*_)
open import Lib.Decidable using (Dec; no; yes)
open import Lib.List using (List; []; _,-_; length)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

-- +N-assoc zero m
-- +N-assoc (suc n) m

-- module _ where
--   foo : (ℕ → ℕ → ℕ) * 𝟚
--   fst foo zero m = m
--   fst foo (suc n) m = suc (fst foo n m)
--   snd foo = tt
--   -- foo = record { fst = 5; snd = tt }
--   -- foo = 5 , tt

-- <F,s,δ>

-- \Sigma
-- \delta

-- <localleader>Sigma
-- <localleader>delta

data SnocList (A : Set) : Set where
  [] : SnocList A
  _-,_ : SnocList A → A → SnocList A

_ : SnocList ℕ
_ = [] -, 5 -, 3 -, 4
-- 534

_ : List ℕ
_ = 5 ,- 3 ,- 4 ,- []
-- 435

infixl 20 _-,_

record Automaton (Σ : Set) (State : Set) : Set1 where
  field
    init : State
    δ : State → Σ → State
    Final : State → Set

  Word : Set
  Word = SnocList Σ

  δ* : State → Word → State
  δ* st [] = st
  δ* st (xs -, x) = δ (δ* st xs) x

  Accept : Word → Set
  Accept word = Final (δ* init word)

  -- δ* st [] = st
  -- δ* st (x ,- xs') = δ* (δ st x) xs'
  -- lem : δ st 'a' ≡ q0


data Letter : Set where
  a b : Letter

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

lengthSL : {A : Set} → SnocList A → ℕ
lengthSL [] = 0
lengthSL (xs -, x) = suc (lengthSL xs)

module Single where
  -- c-c c-c
  -- case split

  data SingleState : Set where
    initial accept err : SingleState

  data FinalStates : SingleState → Set where
    f-accept : FinalStates accept

  single : Automaton Letter SingleState
  Automaton.init single = initial
  Automaton.Final single = FinalStates
  Automaton.δ single err x = err
  Automaton.δ single initial x = accept
  Automaton.δ single accept x = err

  open Automaton single
  -- δ →
  -- δ single

  δ-δ-nothing :
    (c1 c2 : Letter) (st : SingleState) →
    (δ (δ st c1) c2) ≡ err
  δ-δ-nothing c1 c2 initial = refl
  δ-δ-nothing c1 c2 accept = refl
  δ-δ-nothing c1 c2 err = refl

  notFinalErr : FinalStates err → 𝟘
  notFinalErr ()

-- acc : Final (δ (δ (δ* (just ff) w) x1) x)o
-- acc : Final nothing
-- acc : Zero
  correct : (w : Word) → Accept w → lengthSL w ≡ 1
  correct [] ()
  correct ([] -, x) acc = refl
  correct (w -, x1 -, x) acc
    rewrite δ-δ-nothing x1 x (δ* initial w) =
    zero-elim (notFinalErr acc)

  complete : (w : Word) → lengthSL w ≡ 1 → Accept w
  complete [] ()
  complete ([] -, c) x = f-accept
  complete (w -, c1 -, c) ()
  {-
  -}




-- TODO: copatterns
-- * useful for function fields
-- TODO: record modules
-- * can add defs to records
-- * can then open them like modules
-- TODO: Automaton definition
-- * interactive?
-- * unicode, \ in vscode, <localleader> in vim, \ in emacs
-- * Final as "subset"
-- * Set levels
-- * snoclist, why?
-- * Word
-- * correctness and completeness
-- * "onlya" as example
-- * states and finality can be both calculated, and defined

-- TASK
-- Define an automaton that only accepts the empty string
-- Formulate and prove its correctness and completeness
module Empty where
  data State : Set where
    initial other : State
  data Final : State → Set where
    f-accept : Final initial
  empty : Automaton 𝟙 State
  Automaton.init empty = initial
  Automaton.δ empty _ _ = other
  Automaton.Final empty initial = 𝟙
  Automaton.Final empty other = 𝟘

data Even : ℕ → Set where
  e-zero : Even 0
  e-sucsuc : {n : ℕ} → Even n → Even (suc (suc n))

{-
-- TASK
-- Define an automaton that only accepts strings of even length.
-- Formulte and prove its correctness and completeness
module IsEven where

-- TASK
-- Define an automaton that only accepts strings of the form
-- "some number of as followed by some number of bs", i.e. what the regex a*b* would correspond to.
-- Formulate and prove its correctness and completeness.
--
-- HINT: You'll most likely need to define some extra operations on SnocLists to formulate
-- correctness and completeness.
module a*b* where

-- TASK
-- Define the "or automaton" of two automata, in the sense that
-- it accepts strings that either of the input automatons would accept, and nothing else.
-- Formulate and prove its correctness and completeness.
--
-- To make things easier, I've parametrised the module for this task accordingly,
-- as well as opened and renamed some definitions.
module Or {St1 St2 Sym : Set} (Aut1 : Automaton Sym St1) (Aut2 : Automaton Sym St2) where
  open Automaton Aut1 using () renaming
    (
      Final to Final1;
      initial to initial1;
      δ to δ1;
      δ* to δ*1;
      Accept to Accept1
    )
  open Automaton Aut2 using () renaming
    (
      Final to Final2;
      initial to initial2;
      δ to δ2;
      δ* to δ*2;
      Accept to Accept2
    )

-- TASK
-- Define an automaton that only accepts words which have an even number of "changes" in them.
-- A change is defined as a letter being followed by a different one. For example
-- "101" has 2 changes, since we go from 1 to 0, and then from 0 to 1 again.
-- "1111000111" has 2 changes, for the same reason.
-- "101110100" has 5 changes
-- The empty word has zero changes, since there are no letters from which to change or which to change to.
--
-- HINT: You might need to also define an additional predicate to encode how many changes
-- there are in a word, to make your formulations and proofs simpler.
module EvenChanges where
-}
