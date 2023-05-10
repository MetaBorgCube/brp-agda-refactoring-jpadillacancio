module Examples where

open import Typesystem
open import Data.Integer.Base using (ℤ)
open import Semantics

add1 : ∀ {Γ} → Γ ⊢ IntTy ⇒ IntTy
add1 = ƛ (Int ℤ.pos 1) + (var Z) 

matchJust : ∀ {Γ} → Γ ⊢ Maybe IntTy ⇒ IntTy
matchJust = ƛ (caseM (var Z) of
    NothingP to Int (ℤ.pos 0)
    or
    JustP to (add1 · ((var Z))))

ver1 : ∀ {Γ} {γ : Env Γ} → γ ⊢e Int (ℤ.pos 1) ↓ IntV (ℤ.pos 1)
ver1 = ↓Int

verƛ : ∀ {Γ} {γ : Env Γ} → γ ⊢e add1 ↓ ClosV {Γ} {_} {_} γ ((Int ℤ.pos 1) + (var Z))
verƛ = ↓ƛ 

--ver1+1 : ∀ {Γ} {γ : Env Γ} → γ ⊢e (Int {!   !}) + (Int {!   !}) ↓ {!   !} 

verƛ·1 : ∀ {Γ} {γ : Env Γ} {γ-wut : Env (Γ , IntTy)} → γ ⊢e add1 · (Int ℤ.pos 1) ↓ IntV (ℤ.pos 2)
verƛ·1 = ↓· {_} {_} {_} {_} {_} {_} {_} {{!   !}} ↓ƛ (↓+ {_} {_} {_} {_} {_} {_} ↓Int (↓var Z))

{-
-}
 