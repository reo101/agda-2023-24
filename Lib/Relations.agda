open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

-- Heterogeneous binary relations

REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations

Rel : ∀ {a b} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = REL A A ℓ
