module Project.Postulates where

open import Level using (Level)

open import Project.Control.Equality using (_≡_)

postulate
  -- Functional Extensionality
  funext :
    {l₁ l₂ : Level}
    {A : Set l₁}
    {B : A → Set l₂}
    {f g : (x : A) → B x} →
    -----------------------
    ((x : A) → f x ≡ g x) →
    -----------------------
    f ≡ g
