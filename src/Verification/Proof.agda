module Proof where

open import Typesystem
open import Semantics
open import Refactor using (refactorList ; refactorListH ; mapContext ; MaybeTy→ListTy)
open import Agda.Builtin.TrustMe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)

lengthClosEnv : ∀ {aTy rTy} → Value (aTy ⇒ rTy) → ℕ
lengthClosEnv (ClosV {Γ-clos} nv fd) = length Γ-clos

sizeMattersProof : 
    ∀ {Γ aTy rTy} {nv : Env Γ} {fd : Γ ∋ aTy ⇒ rTy} 
    → (lCl : ℕ) → {lCl ≡ lengthClosEnv (nv fd)} 
    → (lCtx : ℕ) → {lCtx ≡ length Γ} 
    → lCl < lCtx
sizeMattersProof zero zero = {!   !}
sizeMattersProof zero (suc lCtxP) = {!   !}
sizeMattersProof (suc lClP) lCtxP = {!   !}

{-# TERMINATING #-}
updateEnv : ∀ {Γ} → Env Γ → Env (mapContext Γ MaybeTy→ListTy)

updateValue : ∀ {ty} → Value ty → Value (MaybeTy→ListTy ty)
updateValue NothingV = NilV
updateValue (JustV v) = ConsV (updateValue v) NilV
updateValue (IntV x) = IntV x
updateValue NilV = NilV
updateValue (ConsV v v₁) = ConsV (updateValue v) (updateValue v₁)
updateValue (LeftV v) = LeftV (updateValue v)
updateValue (RightV v) = RightV (updateValue v)
updateValue (ClosV  nv fd) = ClosV (updateEnv nv) (refactorListH fd) 

updateEnv {∅} nv = ∅'
updateEnv {Γ , ty} nv = updateEnv (λ x → nv (S x)) ,' updateValue (nv Z)

verifySemanticEqH : ∀ {Γ ty} {γ : Env Γ} {v : Value ty} {e : Γ ⊢ ty} → γ ⊢e e ↓ v →  updateEnv γ ⊢e refactorListH e ↓ updateValue v
verifySemanticEqH {Γ} {ty} {γ} {v} (↓var x) = {!  !}
verifySemanticEqH ↓ƛ = ↓ƛ
verifySemanticEqH (↓· p p₁ p₂) = ↓· (verifySemanticEqH p) (verifySemanticEqH p₁) (verifySemanticEqH p₂)
verifySemanticEqH ↓Int = ↓Int
verifySemanticEqH (↓+ p p₁) = ↓+ (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓- p p₁) = ↓- (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓* p p₁) = ↓* (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH ↓Nothing = ↓[]
verifySemanticEqH (↓Just p) = ↓:: (verifySemanticEqH p) ↓[]
verifySemanticEqH ↓[] = ↓[]
verifySemanticEqH (↓:: p p₁) = ↓:: (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓Left p) = ↓Left (verifySemanticEqH p)
verifySemanticEqH (↓Right p) = ↓Right (verifySemanticEqH p)
verifySemanticEqH (↓caseMJ p p₁) = ↓caseL:: (verifySemanticEqH p) {! verifySemanticEqH {?} ?   !}
verifySemanticEqH (↓caseMN p p₁) = ↓caseL[] (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓caseL:: p p₁) = ↓caseL:: (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓caseL[] p p₁) = ↓caseL[] (verifySemanticEqH p) (verifySemanticEqH p₁)

verifySemanticEq : ∀  {ty} {v : Value ty} {e : ∅ ⊢ ty} → ∅' ⊢e e ↓ v → ∅' ⊢e refactorList e ↓ updateValue v
verifySemanticEq d = {!   !}   