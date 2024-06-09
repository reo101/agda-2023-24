module Homework.PropCalc.PropCalc where

open import Level using (Level; zero; suc)

open import Project.Control.Equality using (_≡_; refl; sym; cong; cong-app; trans; subst; ≡-equiv)
open import Project.EquationalReasoning as EquationalReasoning
open module ≡-Reasoning {n} {A} =
       EquationalReasoning.Core {n} {A} _≡_ {{≡-equiv}}
         using (begin_; _∼⟨⟩_; step-∼; _∎)

open import Project.Postulates using (funext)

open import Lib.Two using (𝟚; tt; ff; not; _∧_; _∨_)
open import Lib.Utils using (_∘_)

-- TASK
-- Prove _∧_ commutative
∧-commut : (b1 b2 : 𝟚) → b1 ∧ b2 ≡ b2 ∧ b1
∧-commut tt tt = refl
∧-commut tt ff = refl
∧-commut ff tt = refl
∧-commut ff ff = refl

-- TASK
-- Prove _∧_ associative
∧-assoc : (b1 b2 b3 : 𝟚) → (b1 ∧ b2) ∧ b3 ≡ b1 ∧ (b2 ∧ b3)
∧-assoc tt b2 b3 = refl
∧-assoc ff b2 b3 = refl

-- TASK
-- Formulate and prove the fact that _∨_ is commutative
∨-commut : (b1 b2 : 𝟚) → b1 ∨ b2 ≡ b2 ∨ b1
∨-commut tt tt = refl
∨-commut tt ff = refl
∨-commut ff tt = refl
∨-commut ff ff = refl

-- TASK
-- State assocativity of ∨ and prove it
∨-assoc : (b1 b2 b3 : 𝟚) → (b1 ∨ b2) ∨ b3 ≡ b1 ∨ (b2 ∨ b3)
∨-assoc tt b2 b3 = refl
∨-assoc ff b2 b3 = refl

-- TASK
-- Formulate and prove De Morgan's laws

-- ¬(a ∧ b) ↔ (¬a ∨ ¬b)
dm1 : (b1 b2 : 𝟚) → not (b1 ∧ b2) ≡ not b1 ∨ not b2
dm1 tt b2 = refl
dm1 ff b2 = refl

-- ¬(a ∨ b) ↔ (¬a ∧ ¬b)
dm2 : (b1 b2 : 𝟚) → not (b1 ∨ b2) ≡ not b1 ∧ not b2
dm2 tt b2 = refl
dm2 ff b2 = refl

-- TASK
-- Define the structure of simple propositional expressions.
-- We want to support
--  1. a "false" value
--  2. a "true" value
--  3. "negating" a PropExpr
--  4. "or-ing" two PropExprs
--  5. "and-ing" two PropExprs
data PropExpr : Set where
  echt falsch : PropExpr
  нет_ : PropExpr → PropExpr
  _かつ_ _またわ_ : PropExpr → PropExpr → PropExpr

-- TASK
-- You should be able to "convert" a boolean to a PropExpr
𝟚-to-PropExpr : 𝟚 → PropExpr
𝟚-to-PropExpr tt = echt
𝟚-to-PropExpr ff = falsch

-- TASK
-- Execute a PropExpr by using the boolean operations that the constructors are named after
interpProp : PropExpr → 𝟚
interpProp echt = tt
interpProp falsch = ff
interpProp (нет x) = not (interpProp x)
interpProp (x かつ y) = interpProp x ∧ interpProp y
interpProp (x またわ y) = interpProp x ∨ interpProp y

-- TASK
-- Formulate and prove that if you take two 𝟚s, 𝟚-to-Propexpr them, combine them with your "and" constructor, and interpret them,
-- the result is the same as just simply _∧_-ing the original 𝟚s
homomorphism : (b1 b2 : 𝟚) → interpProp ((𝟚-to-PropExpr b1) かつ (𝟚-to-PropExpr b2)) ≡ b1 ∧ b2
homomorphism tt tt = refl
homomorphism tt ff = refl
homomorphism ff b2 = refl

-- TASK
-- Define the NAND operation over bools
nand𝟚 : 𝟚 → 𝟚 → 𝟚
nand𝟚 tt tt = ff
nand𝟚 tt ff = tt
nand𝟚 ff tt = tt
nand𝟚 ff ff = tt

-- TASK
-- Define ff using tt and NAND
nandff : 𝟚
nandff = nand𝟚 tt tt

-- TASK
-- Formulate and prove that nandff is the same thing as ff
ff≡nandff : ff ≡ nandff
ff≡nandff = refl

-- TASK
-- Define negation using only nand𝟚 and any previously defined operations involving nand.
nandNot : 𝟚 → 𝟚
nandNot b = nand𝟚 b b

-- TASK
-- Formulate and prove that nandNot behaves the same way as not
not≡nandNot : not ≡ nandNot
not≡nandNot = funext λ { tt → refl
                       ; ff → refl }

-- TASK
-- Define _∧_ using only nand𝟚 and any previously defined operations involving nand.
nandAnd : 𝟚 → 𝟚 → 𝟚
nandAnd b1 b2 = nandNot (nand𝟚 b1 b2)

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _∧_
_∧_≡nandAnd : _∧_ ≡ nandAnd
_∧_≡nandAnd = funext λ { tt → funext λ { tt → refl
                                       ; ff → refl }
                       ; ff → funext λ { tt → refl
                                       ; ff → refl } }

-- TASK
-- Define _∨_ using only nand𝟚 and any previously defined operations involving nand.
nandOr : 𝟚 → 𝟚 → 𝟚
nandOr b1 b2 = nandNot (nandAnd (nandNot b1) (nandNot b2))

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _∨_
_∨_≡nandOr : _∨_ ≡ nandOr
_∨_≡nandOr = funext λ { tt → funext λ { tt → refl
                                      ; ff → refl }
                      ; ff → funext λ { tt → refl
                                      ; ff → refl } }

-- TASK
-- Define the structure of "nand expressions", meaning minimal boolean expressions expresed purely via NAND.
-- We want to support
--   1. a "true" value
--   2. the NAND of two NandExprs
data NandExpr : Set where
  本物 : NandExpr
  NandNand : NandExpr → NandExpr → NandExpr

-- TASK
-- Execute a NandExpr
interpNand : NandExpr → 𝟚
interpNand 本物 = tt
interpNand (NandNand b1 b2) = nand𝟚 (interpNand b1) (interpNand b2)

-- TASK
-- Transpile a PropExpr to a NandExpr

NandFf : NandExpr
NandFf = NandNand 本物 本物

ff≡NandFf : ff ≡ interpNand NandFf
ff≡NandFf = refl

NandNot : NandExpr → NandExpr
NandNot b = NandNand b b

-- not≡NandNot : (b1 : NandExpr) → not (interpNand b1) ≡ interpNand (NandNot b1)
-- not≡NandNot 本物 = refl
-- not≡NandNot (NandNand b1 b2) =
--   begin
--     not (interpNand (NandNand b1 b2))
--   ∼⟨ ? ⟩
--     interpNand (NandNot (NandNand b1 b2))
--   ∎

NandAnd : NandExpr → NandExpr → NandExpr
NandAnd b1 b2 = NandNot (NandNand b1 b2)

-- _∧_≡NandAnd : _∧_ ≡ NandAnd
-- _∧_≡NandAnd = funext λ { tt → funext λ { tt → refl
--                                        ; ff → refl }
--                        ; ff → funext λ { tt → refl
--                                        ; ff → refl } }

NandOr : NandExpr → NandExpr → NandExpr
NandOr b1 b2 = NandNot (NandAnd (NandNot b1) (NandNot b2))

-- _∨_≡NandOr : _∨_ ≡ NandOr
-- _∨_≡NandOr = funext λ { tt → funext λ { tt → refl
--                                       ; ff → refl }
--                       ; ff → funext λ { tt → refl
--                                       ; ff → refl } }

Prop-to-Nand : PropExpr → NandExpr
Prop-to-Nand echt = 本物
Prop-to-Nand falsch = NandFf
Prop-to-Nand (нет b) = NandNot (Prop-to-Nand b)
Prop-to-Nand (b1 かつ b2) = NandAnd (Prop-to-Nand b1) (Prop-to-Nand b2)
Prop-to-Nand (b1 またわ b2) = NandOr (Prop-to-Nand b1) (Prop-to-Nand b2)

-- TASK
-- Formulate and prove that your Prop-to-Nand transpilation is correct in terms of interpProp and interpNand,
-- i.e. if you take a PropExpr, translate it to a NandExpr, and then interpNand it,
-- the result should be he same as interpProp-ing the original expression
takovata : ∀ {x} -> interpProp x ≡ interpNand (Prop-to-Nand x)
takovata {echt} = refl
takovata {falsch} = refl
takovata {нет x} =
  begin
    interpProp (нет x)
  ∼⟨⟩
    not (interpProp x)
  ∼⟨ cong not (takovata {x}) ⟩
    not (interpNand (Prop-to-Nand x))
  ∼⟨ cong-app not≡nandNot _ ⟩
    nandNot (interpNand (Prop-to-Nand x))
  -- ∼⟨⟩
  --   nand𝟚 (interpNand (Prop-to-Nand x)) (interpNand (Prop-to-Nand x))
  -- ∼⟨⟩
  --   interpNand (NandNand (Prop-to-Nand x) (Prop-to-Nand x))
  -- ∼⟨⟩
  --   interpNand (NandNot (Prop-to-Nand x))
  ∼⟨⟩
    interpNand (Prop-to-Nand (нет x))
  ∎
takovata {b1 かつ b2} =
  begin
    interpProp (b1 かつ b2)
  ∼⟨⟩
    interpProp b1 ∧ interpProp b2
  ∼⟨ cong (interpProp b1 ∧_) (takovata {b2}) ⟩
    interpProp b1 ∧ interpNand (Prop-to-Nand b2)
  ∼⟨ cong-app (cong _∧_ (takovata {b1})) _ ⟩
    interpNand (Prop-to-Nand b1) ∧ interpNand (Prop-to-Nand b2)
  ∼⟨ cong-app (cong-app _∧_≡nandAnd _) _ ⟩
    nandAnd (interpNand (Prop-to-Nand b1))
            (interpNand (Prop-to-Nand b2))
  -- ∼⟨⟩
  --   nandNot (nand𝟚 (interpNand (Prop-to-Nand b1))
  --                  (interpNand (Prop-to-Nand b2)))
  -- ∼⟨⟩
  --   nand𝟚 (interpNand (NandNand (Prop-to-Nand b1)
  --                               (Prop-to-Nand b2)))
  --         (interpNand (NandNand (Prop-to-Nand b1)
  --                               (Prop-to-Nand b2)))
  -- ∼⟨⟩
  --   interpNand (NandNand (NandNand (Prop-to-Nand b1)
  --                                  (Prop-to-Nand b2))
  --                        (NandNand (Prop-to-Nand b1)
  --                                  (Prop-to-Nand b2)))
  -- ∼⟨⟩
  --   interpNand (NandNot (NandNand (Prop-to-Nand b1)
  --                                 (Prop-to-Nand b2)))
  -- ∼⟨⟩
  --   interpNand (NandAnd (Prop-to-Nand b1)
  --                       (Prop-to-Nand b2))
  ∼⟨⟩
    interpNand (Prop-to-Nand (b1 かつ b2))
  ∎
takovata {b1 またわ b2} =
  begin
    interpProp (b1 またわ b2)
  ∼⟨⟩
    interpProp b1 ∨ interpProp b2
  ∼⟨ cong (interpProp b1 ∨_) (takovata {b2}) ⟩
    interpProp b1 ∨ interpNand (Prop-to-Nand b2)
  ∼⟨ cong-app (cong _∨_ (takovata {b1})) _ ⟩
    interpNand (Prop-to-Nand b1) ∨ interpNand (Prop-to-Nand b2)
  ∼⟨ cong-app (cong-app _∨_≡nandOr _) _ ⟩
    nandOr (interpNand (Prop-to-Nand b1))
           (interpNand (Prop-to-Nand b2))
  -- ∼⟨⟩
  -- ...
  ∼⟨⟩
    interpNand (Prop-to-Nand (b1 またわ b2))
  ∎
