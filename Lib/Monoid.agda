module Lib.Monoid where

record Monoid {a} (A : Set a) : Set a where
  field
    mempty : A
    _<>_   : A → A → A

open Monoid {{...}} public
