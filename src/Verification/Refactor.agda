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

MaybeTy→ListTy : Type → Type
MaybeTy→ListTy (MaybeTy t) = ListTy (MaybeTy→ListTy t)
MaybeTy→ListTy IntTy = IntTy
MaybeTy→ListTy (ty₁ ⇒ ty₂) = MaybeTy→ListTy ty₁ ⇒ MaybeTy→ListTy ty₂
MaybeTy→ListTy (ListTy ty₁) = ListTy (MaybeTy→ListTy ty₁)
MaybeTy→ListTy (EitherTy ty₁ ty₂) = EitherTy (MaybeTy→ListTy ty₁) (MaybeTy→ListTy ty₂)
MaybeTy→ListTy (PatternTy JustPattern) = PatternTy ::Pattern
MaybeTy→ListTy (PatternTy NothingPattern) = PatternTy []Pattern
MaybeTy→ListTy (PatternTy pat) = PatternTy pat

mapContext : ∀ {n} → Context n → (Type → Type) → Context n
mapContext ∅ _ = ∅
mapContext (Γ , x) f = (mapContext Γ f , f x)

update∋PostMap : ∀ {ty n f} {Γ : Context n} → Γ ∋ ty → (mapContext Γ f)  ∋ f ty
update∋PostMap Z = Z
update∋PostMap (S l) = S update∋PostMap l

insertTypeAtIdx : ∀ {l} → (Γ : Context l) → (n : ℕ) → (p : n ≤ l) → (ignoreTy : Type) → Context (suc l)
insertTypeAtIdx Γ zero _ ty = Γ , ty
insertTypeAtIdx (Γ , x) (suc n) (s≤s p) ty = insertTypeAtIdx Γ n p ty , x

-- unify with other helper function to generic fun
update∋PostInsert : ∀ {ty l n p iTy} {Γ : Context l} → Γ ∋ ty → insertTypeAtIdx Γ n p iTy ∋ ty
update∋PostInsert {n = zero} l = S l 
update∋PostInsert {n = suc n} {s≤s p} Z = Z
update∋PostInsert {n = suc n} {s≤s p} (S l) = S update∋PostInsert l

-- enforce that insertion can only be as large as Γ 
insertIgnoredType : ∀ {l ty} {Γ : Context l} →  Γ ⊢ ty → {n : ℕ} → {p : n ≤ l} → {ignoreTy : Type} → insertTypeAtIdx Γ n p ignoreTy ⊢ ty
insertIgnoredType (var x) {zero}  = var (S x)
insertIgnoredType (var x) {suc n}  = var (update∋PostInsert x)
insertIgnoredType (ƛ ex) {n} {p}  = ƛ (insertIgnoredType ex {suc n} {s≤s p} )
insertIgnoredType (ex · ex₁)  = insertIgnoredType ex  · insertIgnoredType ex₁ 
insertIgnoredType (Int x)  = Int x
insertIgnoredType (ex + ex₁)  = insertIgnoredType ex  + insertIgnoredType ex₁ 
insertIgnoredType (ex - ex₁)  = insertIgnoredType ex  - insertIgnoredType ex₁ 
insertIgnoredType (ex * ex₁)  = insertIgnoredType ex  * insertIgnoredType ex₁ 
insertIgnoredType Nothing  = Nothing
insertIgnoredType (Just ex)  = Just (insertIgnoredType ex )
insertIgnoredType []  = []
insertIgnoredType (ex :: ex₁)  = insertIgnoredType ex  :: insertIgnoredType ex₁ 
insertIgnoredType (Left ex)  = Left (insertIgnoredType ex )
insertIgnoredType (Right ex)  = Right (insertIgnoredType ex )
insertIgnoredType (caseM ex of ex₁ to ex₂ or ex₃ to ex₄) {n} {p}  = caseM insertIgnoredType ex  of 
    insertIgnoredType ex₁  to insertIgnoredType ex₂  
    or 
    insertIgnoredType ex₃  to insertIgnoredType ex₄ {suc n} {s≤s p} 
insertIgnoredType (caseL ex of ex₁ to ex₂ or ex₃ to ex₄) {n} {p}  = caseL insertIgnoredType ex  of 
    insertIgnoredType ex₁  to insertIgnoredType ex₂  
    or 
    insertIgnoredType ex₃  to insertIgnoredType ex₄ {suc (suc n)} {s≤s (s≤s p)} 
insertIgnoredType JustP  = JustP
insertIgnoredType NothingP   = NothingP
insertIgnoredType ::P   = ::P
insertIgnoredType []P   = []P

refactorListH : ∀ {l ty₁} {Γ : Context l} → Γ ⊢ ty₁ → (mapContext Γ MaybeTy→ListTy) ⊢ (MaybeTy→ListTy ty₁)
refactorListH (var x) = var (update∋PostMap x)
refactorListH (ƛ e) = ƛ (refactorListH e)
refactorListH (_·_ {A = aTy} {B = rTy} e e₁) = _·_ {A = MaybeTy→ListTy aTy} {B = MaybeTy→ListTy rTy} (refactorListH e) (refactorListH e₁)
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
refactorListH (caseM_of_to_or_to_ {A = A} matchOn nothingP nothingClause justP justClause) = 
    caseL refactorListH matchOn of 
        refactorListH nothingP to refactorListH nothingClause 
        or 
        refactorListH justP to insertIgnoredType (refactorListH justClause) {n = zero} {p = z≤n} {ignoreTy = ListTy (MaybeTy→ListTy A)}
refactorListH (caseL e of e₁ to e₂ or e₃ to e₄) = 
    caseL refactorListH e of 
        refactorListH e₁ to refactorListH e₂ 
        or 
        refactorListH e₃ to refactorListH e₄
refactorListH JustP = ::P
refactorListH NothingP = []P
refactorListH ::P = ::P
refactorListH []P = []P

refactorList : ∀ {ty₁} → ∅ ⊢ ty₁ → ∅ ⊢ (MaybeTy→ListTy ty₁)
refactorList term = refactorListH term  