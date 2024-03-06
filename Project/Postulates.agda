module Project.Postulates where

open import Agda.Primitive using (Level)

open import Lib.Equality using (_≡_)

postulate
  -- Functional Extensionality
  funext :
    {l₁ l₂ : Level}
    {A : Set l₁}
    {B : A → Set l₂}
    {f g : (x : A) → B x}
    (_ : (x : A) → f x ≡ g x)
    → -----------------------
    f ≡ g
