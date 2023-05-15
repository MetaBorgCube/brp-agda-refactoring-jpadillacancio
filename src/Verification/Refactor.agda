module Refactor where

open import Typesystem
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_)

updateType : Type → Type
updateType (Maybe t) = List updateType t
updateType IntTy = IntTy
updateType (ty₁ ⇒ ty₂) = updateType ty₁ ⇒ updateType ty₂
updateType (List ty₁) = List updateType ty₁
updateType (EitherTy ty₁ ty₂) = EitherTy (updateType ty₁) (updateType ty₂)
updateType (PatternTy JustPattern) = PatternTy ::Pattern
updateType (PatternTy NothingPattern) = PatternTy []Pattern
updateType (PatternTy pat) = PatternTy pat

updateContext : Context → Context
updateContext ∅ = ∅
updateContext (Γ , x) = (updateContext Γ , updateType x)

convertLookup : ∀ {ty Γ} → Γ ∋ ty → updateContext Γ ∋ updateType ty
convertLookup Z = Z
convertLookup (S l) = S convertLookup l

convertJustƛ-body :  ∀ { Γ A aTy rTy }   → Γ , A , aTy ⊢ rTy → updateContext Γ , updateType A , (List updateType A), updateType aTy ⊢ updateType rTy
convertJustƛ-body (var Z) = var Z
convertJustƛ-body (var (S Z)) = var (S (S Z))
convertJustƛ-body (var (S (S x))) = var (S (S (S convertLookup x)))
convertJustƛ-body (ƛ e) = {!   !}
convertJustƛ-body (e · e₁) = {!   !}
convertJustƛ-body (Int x) = {!   !}
convertJustƛ-body (e + e₁) = {!   !}
convertJustƛ-body (e - e₁) = {!   !}
convertJustƛ-body (e * e₁) = {!   !}
convertJustƛ-body Nothing = {!   !}
convertJustƛ-body (Just e) = {!   !}
convertJustƛ-body [] = {!   !}
convertJustƛ-body (e :: e₁) = {!   !}
convertJustƛ-body (Left e) = {!   !}
convertJustƛ-body (Right e) = {!   !}
convertJustƛ-body (caseM e of e₁ to e₂ or e₃ to e₄) = {!   !}
convertJustƛ-body (caseL e of e₁ to e₂ or e₃ to e₄) = {!   !}
convertJustƛ-body JustP = {!   !}
convertJustƛ-body NothingP = {!   !}
convertJustƛ-body ::P = {!   !}
convertJustƛ-body []P = {!   !}

convertJustClause : ∀ { Γ A B } → Γ , A ⊢ B →  updateContext Γ , updateType A , List updateType A ⊢ updateType B
convertJustClause (var x) = var (S convertLookup x)
convertJustClause (ƛ {_} {aTy} {rTy} e) = ƛ {!    !}
convertJustClause (e · e₁) = convertJustClause e · convertJustClause e₁
convertJustClause (Int x) = Int x
convertJustClause (e + e₁) = convertJustClause e + convertJustClause e₁
convertJustClause (e - e₁) = convertJustClause e - convertJustClause e₁
convertJustClause (e * e₁) = convertJustClause e * convertJustClause e₁
convertJustClause Nothing = []
convertJustClause (Just e) = convertJustClause e :: []
convertJustClause [] = []
convertJustClause (e :: e₁) = convertJustClause e :: convertJustClause e₁
convertJustClause (Left e) = Left (convertJustClause e)
convertJustClause (Right e) = Right (convertJustClause e)
convertJustClause (caseM matchOn of nothingP to nothingClause or justP to justClause) = {!    !}
convertJustClause (caseL matchOn of []Pat to []Clause or ::Pat to ::Clause) = {!   !}
convertJustClause JustP = ::P
convertJustClause NothingP = []P
convertJustClause ::P = ::P
convertJustClause []P = []P

-- If ty1 is a Maybe then ty2 is a list else ty1 == ty2
-- Either (ty1=M → ty2=L) (ty1=ty2) 
refactorListH : ∀ {Γ  ty₁} → Γ ⊢ ty₁ → (updateContext Γ) ⊢ (updateType ty₁)
refactorListH (var x) = var (convertLookup x)
refactorListH (ƛ {_} {aTy} {rTy} e) = ƛ (refactorListH e)
refactorListH { Γ } { ty } (_·_ {_} {aTy} {rTy} e e₁) = _·_ {_} {updateType aTy} {updateType rTy} (refactorListH e) (refactorListH e₁)
refactorListH (Int x) = Int x
refactorListH (e + e₁) = refactorListH e + refactorListH e₁
refactorListH (e - e₁) = refactorListH e - refactorListH e₁
refactorListH (e * e₁) = refactorListH e * refactorListH e₁
refactorListH Nothing = []
refactorListH (Just e) = refactorListH e :: []
refactorListH [] = []
refactorListH (e :: e₁) = refactorListH e :: refactorListH e₁
refactorListH (Left e) = Left (refactorListH e)
refactorListH (Right e) = Right (refactorListH e)
refactorListH {_} {rTy} (caseM matchOn of nothingP to nothingClause or justP to justClause) = 
    caseL refactorListH matchOn of 
        refactorListH nothingP to refactorListH nothingClause 
        or 
        refactorListH justP to convertJustClause justClause
refactorListH (caseL e of e₁ to e₂ or e₃ to e₄) = 
    caseL refactorListH e of refactorListH 
        e₁ to refactorListH e₂ 
        or 
        refactorListH e₃ to refactorListH e₄
refactorListH JustP = ::P
refactorListH NothingP = []P
refactorListH ::P = ::P
refactorListH []P = []P

refactorList : ∀ {ty₁} → ∅ ⊢ ty₁ → ∅ ⊢ (updateType ty₁)
refactorList term = refactorListH term 