module Lib.Default where

record Default (A : Set) : Set where
  field
    default : A

open Default {{...}} public
