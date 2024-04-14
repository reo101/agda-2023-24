module Lib.List where

open import Lib.Nat using (ℕ; zero; suc; ozero; osuc; _+_; _≤_)
open import Lib.Sigma using (Σ)
open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎;
                reflexive; symmetric; transitive)

data List (A : Set) : Set where
  -- the empty list is a list
  [] : List A
  -- we can add a new element to the "head" of a list
  _,-_ : A → List A → List A

infixr 20 _,-_

_+L_ : {A : Set} → List A → List A → List A
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

infixr 25 _+L_

+L-assoc : {A : Set} (xs ys zs : List A) → (xs +L ys) +L zs ≡ xs +L (ys +L zs)
+L-assoc [] ys zs = refl
+L-assoc (x ,- xs) ys zs = cong (x ,-_) (+L-assoc xs ys zs)

+L-right-id : {A : Set} (xs : List A) → xs +L [] ≡ xs
+L-right-id [] = refl
+L-right-id (x ,- xs) rewrite +L-right-id xs = refl

length : {A : Set} → List A → ℕ
length [] = zero
length (_x ,- xs) = suc (length xs)

+L-length : {A : Set} (xs ys : List A) → length (xs +L ys) ≡ length xs + length ys
+L-length [] ys = refl
+L-length (x ,- xs) ys rewrite +L-length xs ys = refl

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ,- xs) = reverse xs +L (x ,- [])

reverse-swap : {A : Set} (xs ys : List A) → reverse (xs +L ys) ≡ reverse ys +L reverse xs
reverse-swap [] ys rewrite +L-right-id (reverse ys) = refl
reverse-swap (x ,- xs) ys =
  begin
    reverse (xs +L ys) +L (x ,- [])
  ∼⟨ cong-app (cong _+L_ (reverse-swap xs ys)) _ ⟩
    (reverse ys +L reverse xs) +L (x ,- [])
  ∼⟨ +L-assoc (reverse ys) (reverse xs) (x ,- []) ⟩
    reverse ys +L reverse xs +L (x ,- [])
  ∎

reverse-reverse-id : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse-id [] = refl
reverse-reverse-id (x ,- xs) =
  begin
    reverse (reverse xs +L (x ,- []))
  ∼⟨ reverse-swap (reverse xs) (x ,- []) ⟩
    x ,- reverse (reverse xs)
  ∼⟨ cong (_,-_ x) (reverse-reverse-id xs) ⟩
    x ,- xs
  ∎
