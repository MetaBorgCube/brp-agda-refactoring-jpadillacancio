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

private 
    variable
        Γ : Context

        ty : Type

        f : Type → Type 

MaybeTy→ListTy : Type → Type
MaybeTy→ListTy (MaybeTy t) = ListTy (MaybeTy→ListTy t)
MaybeTy→ListTy IntTy = IntTy
MaybeTy→ListTy (ty₁ ⇒ ty₂) = MaybeTy→ListTy ty₁ ⇒ MaybeTy→ListTy ty₂
MaybeTy→ListTy (ListTy ty₁) = ListTy (MaybeTy→ListTy ty₁)
MaybeTy→ListTy (PatternTy JustPattern) = PatternTy ::Pattern
MaybeTy→ListTy (PatternTy NothingPattern) = PatternTy []Pattern
MaybeTy→ListTy (PatternTy pat) = PatternTy pat

data Extend_Under_ : Context → (Type → Type) → Set where
    eo-root : Extend ∅ Under f
    eo-elem : Extend Γ Under f → Extend (Γ , ty) Under  f
    eo-pad : Type → Extend Γ Under f → Extend Γ Under f

constructRefContext : Extend Γ Under f → Context
constructRefContext (eo-root) = ∅
constructRefContext (eo-elem {f = f} {ty = ty} ev) = constructRefContext ev , f ty
constructRefContext (eo-pad {f = f} ty ev) = constructRefContext ev , f ty

update∋PostRef : (ev : Extend Γ Under MaybeTy→ListTy) → Γ ∋ ty → (constructRefContext ev) ∋ MaybeTy→ListTy ty  
update∋PostRef eo-root ()
update∋PostRef (eo-elem ev)  Z = Z
update∋PostRef (eo-elem ev)  (S x) = S (update∋PostRef ev x)
update∋PostRef (eo-pad t ev) x = S (update∋PostRef ev x)

refactorListJH : Γ ⊢ ty → (ev : Extend Γ Under MaybeTy→ListTy) → (constructRefContext ev)  ⊢ MaybeTy→ListTy ty
refactorListJH (var x) ev = var (update∋PostRef ev x)
refactorListJH (ƛ t) ev = ƛ (refactorListJH t (eo-elem ev))
refactorListJH (t · t₁) ev = refactorListJH t ev · refactorListJH t₁ ev
refactorListJH (Int x) ev = Int x
refactorListJH (t + t₁) ev = refactorListJH t ev + refactorListJH t₁ ev
refactorListJH (t - t₁) ev = refactorListJH t ev - refactorListJH t₁ ev
refactorListJH (t * t₁) ev = refactorListJH t ev * refactorListJH t₁ ev
refactorListJH Nothing ev = []
refactorListJH (Just t) ev = refactorListJH t ev :: []
refactorListJH [] ev = []
refactorListJH (t :: t₁) ev = refactorListJH t ev :: refactorListJH t₁ ev
refactorListJH (caseM m of nP to nC or jP to jC) ev = caseL refactorListJH m ev of refactorListJH nP ev to refactorListJH nC ev or refactorListJH jP ev to refactorListJH jC (eo-pad (ListTy _) (eo-elem ev))
refactorListJH (caseL m of []Pat to []C or ::Pat to ::C) ev = caseL refactorListJH m ev of refactorListJH []Pat ev to refactorListJH []C ev or refactorListJH ::Pat ev to refactorListJH ::C (eo-elem (eo-elem ev))
refactorListJH JustP ev = ::P
refactorListJH NothingP ev = []P
refactorListJH ::P ev = ::P
refactorListJH []P ev = []P

refactorListJ : ∅ ⊢ ty → (ev : Extend ∅ Under MaybeTy→ListTy) → (constructRefContext ev) ⊢ MaybeTy→ListTy ty
refactorListJ = refactorListJH