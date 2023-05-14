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

-- If ty1 is a Maybe then ty2 is a list else ty1 == ty2
-- Either (ty1=M → ty2=L) (ty1=ty2) 
refactorList : ∀ {Γ ty₁}  →  Γ ⊢ ty₁ → updateContext Γ ⊢ (updateType ty₁)
refactorList {Γ} (var x) = {! var { ? } x  !}
refactorList (ƛ term) = ƛ  refactorList term
refactorList (fun · arg) = refactorList fun · refactorList arg
refactorList (Int x) = Int x
refactorList (term + term₁) = refactorList term + refactorList term₁
refactorList (term - term₁) = refactorList term - refactorList term₁
refactorList (term * term₁) = refactorList term * refactorList term₁
refactorList Nothing = []
refactorList (Just term) = refactorList term :: []
refactorList [] = []
refactorList (term :: term₁) = refactorList term :: refactorList term₁
refactorList (Left term) = Left (refactorList term)
refactorList (Right term) = Left (refactorList term)
refactorList (caseM match of p₁ to term₁ or p₂ to term₃) = 
    caseL refactorList match of 
    refactorList p₁ to refactorList term₁ 
    or 
    refactorList p₂ to {! refactorList term₃ !}
refactorList (caseL match of p₁ to term₁ or p₂ to term₃) = caseL refactorList match of 
    refactorList p₁ to refactorList term₁ 
    or 
    refactorList p₂ to refactorList term₃
refactorList JustP = ::P
refactorList NothingP = []P
refactorList ::P = ::P
refactorList []P = []P