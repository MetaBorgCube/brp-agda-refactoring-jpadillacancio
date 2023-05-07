module Semantics where

open import Agda.Builtin.Int renaming (Int to ℤ)
open import Typesystem

data Value : Set where
    IntV : ℤ → Value
    

data Closure : Set where
    ∅ : Closure
