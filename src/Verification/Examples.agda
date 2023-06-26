module Verification.Examples where

open import Data.Integer using (ℤ) 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Unit using (tt)

open import Typesystem
open import Semantics
open import Refactor
open import Proof

simpleJ : ∅ ⊢ MaybeTy IntTy  
simpleJ = Just (Int ℤ.pos 1)

simpleJRef : refactorList simpleJ eo-root ≡ ((Int ℤ.pos 1) :: [])
simpleJRef = refl

simpleJSem : ∅' ⊢e simpleJ ↓ JustV (IntV (ℤ.pos 1))
simpleJSem = ↓Just ↓Int

simpleJRefSem : ∅' ⊢e refactorList simpleJ eo-root ↓ ConsV (IntV (ℤ.pos 1)) NilV
simpleJRefSem = ↓:: ↓Int ↓[]

getVal : ∀ {Γ ty} {γ : Env Γ} {e : Γ ⊢ ty} {v} → γ ⊢e e ↓ v → Value ty
getVal {v = v} d = v

simpleJRefSemProof : getVal simpleJSem v↦ᵣ getVal simpleJRefSem
simpleJRefSemProof = proof eo-root simpleJSem simpleJRefSem tt