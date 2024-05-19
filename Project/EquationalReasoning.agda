module Project.EquationalReasoning where

open import Level using (Level; _⊔_; suc)

open import Project.Relations using (EquivalenceRelation)

private
  variable
    n m   : Level
    A     : Set n
    x y z : A

module Core (_∼_ : A → A → Set m) {{∼-equiv : EquivalenceRelation _∼_}} where

  open EquivalenceRelation ∼-equiv using (reflexive; symmetric; transitive) public

  infix  1 begin_
  infixr 2 _∼⟨⟩_ step-∼
  infix  3 _∎

  begin_ : ∀ {x y : A} →
           -------------
           x ∼ y →
           -----
           x ∼ y
  begin x∼y = x∼y

  _∼⟨⟩_ : ∀ (x {y} : A) →
          ---------
          x ∼ y →
          -----
          x ∼ y
  x ∼⟨⟩ x∼y = x∼y

  step-∼ : ∀ (x {y z} : A) →
           -----------------
           y ∼ z →
           x ∼ y →
           -------
           x ∼ z
  step-∼ x y∼z x∼y = transitive x∼y y∼z

  syntax step-∼ x y∼z x∼y = x ∼⟨ x∼y ⟩ y∼z

  _∎ : ∀ (x : A) →
      ------------
      x ∼ x
  x ∎ = reflexive
