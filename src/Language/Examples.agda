module Language.Examples where

open import Typesystem
open import Data.Integer.Base using (ℤ)
open import Semantics

add1 : ∀ {Γ} → Γ ⊢ IntTy ⇒ IntTy
add1 = ƛ ((Int ℤ.pos 1) + (# 0)) 

matchJust : ∀ {Γ} → Γ ⊢ Maybe IntTy ⇒ IntTy
matchJust = ƛ (caseM (# 0) of
    NothingP to Int (ℤ.pos 0)
    or
    JustP to (add1 · ((# 0))))

matchList : ∀ {Γ} → Γ ⊢ List IntTy ⇒ IntTy
matchList = ƛ (caseL # 0 of 
    []P to Int ℤ.negsuc 0
    or
    ::P to (# 1))

vermatch:: : ∀ {Γ} {γ : Env Γ} → γ ⊢e matchList · ((Int ℤ.pos 1) :: []) ↓ IntV (ℤ.pos 1)
vermatch:: = ↓· ↓ƛ (↓:: ↓Int ↓[]) (↓caseL:: (↓var Z) (↓var (S Z)))

ver1 : ∀ {Γ} {γ : Env Γ} → γ ⊢e Int (ℤ.pos 1) ↓ IntV (ℤ.pos 1)
ver1 = ↓Int

verƛ : ∀ {Γ} {γ : Env Γ} → γ ⊢e add1 ↓ ClosV {Γ} {_} {_} γ ((Int ℤ.pos 1) + (var Z))
verƛ = ↓ƛ 

ver1+1 : ∀ {Γ} {γ : Env Γ} → γ ⊢e (Int ℤ.pos 1) + (Int ℤ.pos 1) ↓ IntV (ℤ.pos 2) 
ver1+1 = ↓+ ↓Int ↓Int

veradd1·1 : ∀ {Γ} {γ : Env Γ} → γ ⊢e add1 · (Int ℤ.pos 1) ↓ IntV (ℤ.pos 2)
veradd1·1 = ↓· ↓ƛ ↓Int (↓+ ↓Int (↓var Z))

vermatchJust·1 : ∀ {Γ} {γ : Env Γ} → γ ⊢e matchJust · Just (Int ℤ.pos 1) ↓ IntV (ℤ.pos 2)
vermatchJust·1 = ↓· ↓ƛ (↓Just ↓Int) (↓caseMJ (↓var Z) (↓· verƛ (↓var Z) (↓+ ↓Int (↓var Z))))
