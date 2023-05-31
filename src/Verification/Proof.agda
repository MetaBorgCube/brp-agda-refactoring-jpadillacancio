module Proof where

open import Typesystem
open import Semantics
open import Refactor using (refactorList ; refactorListH ; mapContext ; MaybeTy→ListTy ; insertIgnoredType ; insertTypeAtIdx)
open import Agda.Builtin.TrustMe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)


{-# TERMINATING #-}
updateEnv : {n : ℕ} {Γ : Context n} → Env Γ → Env (mapContext Γ MaybeTy→ListTy)

updateValue : {ty : Type} → Value ty → Value (MaybeTy→ListTy ty)
updateValue NothingV = NilV
updateValue (JustV v) = ConsV (updateValue v) NilV
updateValue (IntV x) = IntV x
updateValue NilV = NilV
updateValue (ConsV v v₁) = ConsV (updateValue v) (updateValue v₁)
updateValue (LeftV v) = LeftV (updateValue v)
updateValue (RightV v) = RightV (updateValue v)
updateValue (ClosV  nv fd) = ClosV (updateEnv nv) (refactorListH fd) 

updateEnv {Γ = ∅} nv = ∅'
updateEnv {Γ = Γ , ty} nv = updateEnv (λ x → nv (S x)) ,' updateValue (nv Z)

insertValAtIdx : ∀ {l ty} {Γ : Context l} → (γ : Env Γ) → (n : ℕ) → {p : n ≤ l} → (ignoreVal : Value ty) → Env (insertTypeAtIdx Γ n p ty)
insertValAtIdx γ zero v = γ ,' v
insertValAtIdx {Γ = Γ , x} γ (suc n) {s≤s p} v = insertValAtIdx (Env-tail γ) n v ,' Env-head γ  

insertIgnoredValClos : ∀ {l eTy iTy} {Γ : Context l} → Value eTy → {n : ℕ} → {p : n ≤ l} → Value iTy → Value eTy
insertIgnoredValClos {Γ = Γ} (ClosV γ body) {n = n} {p} v = ClosV (insertValAtIdx {Γ = {!  Γ !}} γ n {{!   !}} v) {! insertTypeAtIdx ? ? ? ? !}
insertIgnoredValClos v _ = v

insertIgnoredVal : ∀ {l eTy iTy} {Γ : Context l} {e : Γ ⊢ eTy} {v : Value eTy} {γ : Env Γ} 
    → γ ⊢e e ↓ v 
    → {n : ℕ} 
    → {p : n ≤ l} 
    → {iVal : Value iTy} 
    → insertValAtIdx γ n {p} iVal ⊢e insertIgnoredType e ↓ {!  insertIgnoredValClos v !}
insertIgnoredVal (↓var x) {n} {p} {iVal} = {!   !}
insertIgnoredVal ↓ƛ {zero} {z≤n} {iVal} = {!   !}
insertIgnoredVal ↓ƛ {suc n} {p} {iVal} = {!   !}
insertIgnoredVal {Γ} (↓· {γ-clos = γ-clos} d d₁ d₂) = ↓· (insertIgnoredVal d) (insertIgnoredVal d₁)  d₂
insertIgnoredVal ↓Int = ↓Int
insertIgnoredVal (↓+ d d₁) = ↓+ (insertIgnoredVal d) (insertIgnoredVal d₁)
insertIgnoredVal (↓- d d₁) = ↓- (insertIgnoredVal d) (insertIgnoredVal d₁)
insertIgnoredVal (↓* d d₁) = ↓* (insertIgnoredVal d) (insertIgnoredVal d₁)
insertIgnoredVal ↓Nothing = ↓Nothing
insertIgnoredVal (↓Just d) = ↓Just (insertIgnoredVal d)
insertIgnoredVal ↓[] = ↓[]
insertIgnoredVal (↓:: d d₁) = ↓:: (insertIgnoredVal d) (insertIgnoredVal d₁)
insertIgnoredVal (↓Left d) = ↓Left (insertIgnoredVal d)
insertIgnoredVal (↓Right d) = ↓Right (insertIgnoredVal d)
insertIgnoredVal (↓caseMJ d d₁) = ↓caseMJ (insertIgnoredVal d) (insertIgnoredVal d₁)
insertIgnoredVal (↓caseMN d d₁) = ↓caseMN (insertIgnoredVal d) (insertIgnoredVal d₁)
insertIgnoredVal (↓caseL:: d d₁) = ↓caseL:: (insertIgnoredVal d) (insertIgnoredVal d₁)
insertIgnoredVal (↓caseL[] d d₁) = ↓caseL[] (insertIgnoredVal d) (insertIgnoredVal d₁) 

verifySemanticEqH : ∀ {l ty} {Γ : Context l} {γ : Env Γ} {v : Value ty} {e : Γ ⊢ ty} → γ ⊢e e ↓ v →  updateEnv γ ⊢e refactorListH e ↓ updateValue v
verifySemanticEqH (↓var x) = {! ↓var ? !}
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
verifySemanticEqH (↓caseMJ p p₁) = ↓caseL:: (verifySemanticEqH p) (insertIgnoredVal (verifySemanticEqH p₁))
verifySemanticEqH (↓caseMN p p₁) = ↓caseL[] (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓caseL:: p p₁) = ↓caseL:: (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓caseL[] p p₁) = ↓caseL[] (verifySemanticEqH p) (verifySemanticEqH p₁)

verifySemanticEq : ∀  {ty} {v : Value ty} {e : ∅ ⊢ ty} → ∅' ⊢e e ↓ v → ∅' ⊢e refactorList e ↓ updateValue v
verifySemanticEq d = verifySemanticEqH d   