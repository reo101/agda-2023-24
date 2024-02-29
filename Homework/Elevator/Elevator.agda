module Homework.Elevator.Elevator where

open import Lib.Zero using (𝟘)
open import Lib.One using (𝟙; ⟨⟩)
open import Lib.Two using (𝟚; tt; ff; not; _&&_; _||_)
open import Lib.Sum using (_+_; inl; inr)

Is : 𝟚 → Set
Is tt = 𝟙
Is ff = 𝟘

data State : Set where
  -- vacant  : State
  -- closing : State
  -- moving  : State
  vacant closing moving : State

eqState : State → State → 𝟚
eqState vacant  vacant  = tt
eqState closing closing = tt
eqState moving  moving  = tt
{-# CATCHALL #-}
eqState _       _       = ff

_=ₛ_ : State → State → 𝟚
_=ₛ_ = eqState

_≠ₛ_ : State → State → 𝟚
_≠ₛ_ = \ s₁ s₂ → not (s₁ =ₛ s₂)

data Action : State -> Set where
  callFrom goTo : Action vacant
  openDoors closeDoors : Action closing
  arrive : Action moving
open Action

eqAction : ∀ {s₁ s₂} → Action s₁ → Action s₂ → 𝟚
eqAction callFrom   callFrom   = tt
eqAction goTo       goTo       = tt
eqAction openDoors  openDoors  = tt
eqAction closeDoors closeDoors = tt
eqAction arrive     arrive     = tt
{-# CATCHALL #-}
eqAction _          _          = ff

_=ₐ_ : ∀ {s₁ s₂} → Action s₁ → Action s₂ → 𝟚
_=ₐ_ = eqAction

_≠ₐ_ : ∀ {s₁ s₂} → Action s₁ → Action s₂ → 𝟚
_≠ₐ_ = \ a₁ a₂ → not (a₁ =ₐ a₂)

transition : (s : State)  → Action s → State
transition vacant  callFrom   = closing
transition vacant  goTo       = closing
transition closing openDoors  = vacant
transition closing closeDoors = moving
transition moving  arrive     = vacant

_ : (a : Action moving) →
    Is (a =ₐ arrive && transition moving a =ₛ vacant)
_ = λ { arrive → ⟨⟩ }

_ : (a : Action vacant) →
    Is (transition vacant a =ₛ closing)
_ = λ { callFrom → ⟨⟩; goTo → ⟨⟩ }
 
_ : (a : Action closing) →
    Is (transition closing a =ₛ vacant || transition closing a =ₛ moving)
_ = λ { openDoors → ⟨⟩; closeDoors → ⟨⟩ }

transition-progress :
  (s : State)
  (a : Action s) →
  Is (s ≠ₛ transition s a)
transition-progress vacant  callFrom   = ⟨⟩
transition-progress vacant  goTo       = ⟨⟩
transition-progress closing openDoors  = ⟨⟩
transition-progress closing closeDoors = ⟨⟩
transition-progress moving  arrive     = ⟨⟩
