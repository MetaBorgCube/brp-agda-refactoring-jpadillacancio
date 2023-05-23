module Refactor where

open import Typesystem
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; z≤n; s≤s)

updateType : Type → Type
updateType (MaybeTy t) = ListTy (updateType t)
updateType IntTy = IntTy
updateType (ty₁ ⇒ ty₂) = updateType ty₁ ⇒ updateType ty₂
updateType (ListTy ty₁) = ListTy (updateType ty₁)
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

insertType : (Γ : Context) →  (n : ℕ) → (p : n ≤ length Γ) → (ignoreTy : Type)  → Context
insertType Γ zero _ ty = Γ , ty
insertType (Γ , x) (suc n) (s≤s p) ty = insertType Γ n p ty , x

-- unify with other helper function to generic fun
convertLookup2 : ∀ {ty Γ n p iTy} → Γ ∋ ty → insertType Γ n p iTy ∋ ty
convertLookup2 {_} {_} {zero} Z = S Z 
convertLookup2 {_} {_} {suc n} {s≤s p} Z = Z
convertLookup2 {_} {_} {zero} (S l) = S (S l)
convertLookup2 {_} {_} {suc n} {s≤s p} (S l) = S convertLookup2 l

-- enforce that insertion can only be as large as Γ 
ignoreConversion : ∀ {Γ  ty} →  Γ ⊢ ty → (n : ℕ) → (p : n ≤ length Γ) → (ignoreTy : Type) → insertType Γ n p ignoreTy ⊢ ty
ignoreConversion (var x) zero p iTy = var (S x)
ignoreConversion (var Z) (suc n) p iTy = var (convertLookup2 Z)
ignoreConversion {Γ} (var (S x)) (suc n) p iTy = var (convertLookup2 (S x))
ignoreConversion (ƛ ex) n p iTy = ƛ (ignoreConversion ex (suc n) (s≤s p) iTy)
ignoreConversion (ex · ex₁) n p iTy = ignoreConversion ex n p iTy · ignoreConversion ex₁ n p iTy
ignoreConversion (Int x) n p iTy = Int x
ignoreConversion (ex + ex₁) n p iTy = ignoreConversion ex n p iTy + ignoreConversion ex₁ n p iTy
ignoreConversion (ex - ex₁) n p iTy = ignoreConversion ex n p iTy - ignoreConversion ex₁ n p iTy
ignoreConversion (ex * ex₁) n p iTy = ignoreConversion ex n p iTy * ignoreConversion ex₁ n p iTy
ignoreConversion Nothing n p iTy = Nothing
ignoreConversion (Just ex) n p iTy = Just (ignoreConversion ex n p iTy)
ignoreConversion [] n p iTy = []
ignoreConversion (ex :: ex₁) n p iTy = ignoreConversion ex n p iTy :: ignoreConversion ex₁ n p iTy
ignoreConversion (Left ex) n p iTy = Left (ignoreConversion ex n p iTy)
ignoreConversion (Right ex) n p iTy = Right (ignoreConversion ex n p iTy)
ignoreConversion (caseM ex of ex₁ to ex₂ or ex₃ to ex₄) n p iTy = caseM ignoreConversion ex n p iTy of 
    ignoreConversion ex₁ n p iTy to ignoreConversion ex₂ n p iTy 
    or 
    ignoreConversion ex₃ n p iTy to ignoreConversion ex₄ (suc n) (s≤s p) iTy
ignoreConversion (caseL ex of ex₁ to ex₂ or ex₃ to ex₄) n p iTy = caseL ignoreConversion ex n p iTy of 
    ignoreConversion ex₁ n p iTy to ignoreConversion ex₂ n p iTy 
    or 
    ignoreConversion ex₃ n p iTy to ignoreConversion ex₄ (suc (suc n)) (s≤s (s≤s p)) iTy
ignoreConversion JustP n p iTy = JustP
ignoreConversion NothingP n p iTy = NothingP
ignoreConversion ::P n p iTy = ::P
ignoreConversion []P n p iTy = []P

I-hate-myself : ∀ {Γ A ty} → Γ , A ⊢ ty → Γ , A , ListTy A ⊢ ty 
I-hate-myself {_} {A} ex = ignoreConversion ex zero z≤n (ListTy A)

-- If ty1 is a MaybeTy then ty2 is a ListTy else ty1 == ty2
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
refactorListH (caseM_of_to_or_to_ {_} {A} matchOn nothingP nothingClause justP justClause) = 
    caseL refactorListH matchOn of 
        refactorListH nothingP to refactorListH nothingClause 
        or 
        refactorListH justP to ignoreConversion (refactorListH justClause) zero z≤n (ListTy (updateType A))
refactorListH (caseL e of e₁ to e₂ or e₃ to e₄) = 
    caseL refactorListH e of 
        refactorListH e₁ to refactorListH e₂ 
        or 
        refactorListH e₃ to refactorListH e₄
refactorListH JustP = ::P
refactorListH NothingP = []P
refactorListH ::P = ::P
refactorListH []P = []P

refactorList : ∀ {ty₁} → ∅ ⊢ ty₁ → ∅ ⊢ (updateType ty₁)
refactorList term = refactorListH term 