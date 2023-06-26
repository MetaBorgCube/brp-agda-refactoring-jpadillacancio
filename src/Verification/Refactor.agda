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

refactorListH : Γ ⊢ ty → (ev : Extend Γ Under MaybeTy→ListTy) → (constructRefContext ev)  ⊢ MaybeTy→ListTy ty
refactorListH (var x) ev = var (update∋PostRef ev x)
refactorListH (ƛ t) ev = ƛ (refactorListH t (eo-elem ev))
refactorListH (t · t₁) ev = refactorListH t ev · refactorListH t₁ ev
refactorListH (Int x) ev = Int x
refactorListH (t + t₁) ev = refactorListH t ev + refactorListH t₁ ev
refactorListH (t - t₁) ev = refactorListH t ev - refactorListH t₁ ev
refactorListH (t * t₁) ev = refactorListH t ev * refactorListH t₁ ev
refactorListH Nothing ev = []
refactorListH (Just t) ev = refactorListH t ev :: []
refactorListH [] ev = []
refactorListH (t :: t₁) ev = refactorListH t ev :: refactorListH t₁ ev
refactorListH (caseM m of nP to nC or jP to jC) ev = caseL refactorListH m ev of refactorListH nP ev to refactorListH nC ev or refactorListH jP ev to refactorListH jC (eo-pad (ListTy _) (eo-elem ev))
refactorListH (caseL m of []Pat to []C or ::Pat to ::C) ev = caseL refactorListH m ev of refactorListH []Pat ev to refactorListH []C ev or refactorListH ::Pat ev to refactorListH ::C (eo-elem (eo-elem ev))
refactorListH JustP ev = ::P
refactorListH NothingP ev = []P
refactorListH ::P ev = ::P
refactorListH []P ev = []P

refactorList : ∅ ⊢ ty → (ev : Extend ∅ Under MaybeTy→ListTy) → (constructRefContext ev) ⊢ MaybeTy→ListTy ty
refactorList = refactorListH