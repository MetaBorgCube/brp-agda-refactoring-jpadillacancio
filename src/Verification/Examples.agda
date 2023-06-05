module Verification.Examples where

open import Data.Integer using (ℤ) 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Typesystem
open import Semantics
open import Refactor

simpleJ : ∅ ⊢ MaybeTy IntTy  
simpleJ = Just (Int ℤ.pos 1)

simpleJRef : refactorList simpleJ ≡ ((Int ℤ.pos 1) :: [])
simpleJRef = refl

simpleJSem : ∅' ⊢e simpleJ ↓ JustV (IntV (ℤ.pos 1))
simpleJSem = ↓Just ↓Int

simpleJRefSem : ∅' ⊢e refactorList simpleJ ↓ ConsV (IntV (ℤ.pos 1)) NilV
simpleJRefSem = ↓:: ↓Int ↓[]


simpleJRefSemP : simpleJRefSem ≡ {! ? ⊢e ? ↓ ?  !}
simpleJRefSemP = {!   !} 