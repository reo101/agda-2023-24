{-# OPTIONS --prop #-}

module Lib.Props where

data ⊥ : Prop where

⊥-elim : ∀ {n} {A : Set n} → ⊥ → A
⊥-elim ()

data ⊤ : Prop where
  ⟨⟩ : ⊤

⊤-intro : ⊤
⊤-intro = ⟨⟩
