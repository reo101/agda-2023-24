module Project.Relations where

open import Level using (Level; zero; suc; _⊔_)

private
  variable
     ℓ₁ ℓ₂ : Level

record EquivalenceRelation {A : Set ℓ₁} (_∼_ : A → A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    reflexive : ∀ {x} →
                -------
                x ∼ x

    symmetric : ∀ {x y} →
                ---------
                x ∼ y →
                -----
                y ∼ x

    transitive : ∀ {x y z} →
                 -----------
                 x ∼ y →
                 y ∼ z →
                 -----
                 x ∼ z

open EquivalenceRelation public
