module Proof where

open import Typesystem
open import Semantics
open import Refactor using (refactorListJ ; refactorListJH  ; MaybeTy→ListTy ; constructRefContext ; Extend_Under_ ; eo-root ; eo-elem ; eo-pad ; update∋PostRef) 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)  
open import Data.Nat using (ℕ; zero; suc; _<_; _>_ ; _≤_; _≥_; z≤n; s≤s ; _>?_) renaming (_+_ to _+ₙ_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import Data.Integer using (ℤ; -≤-; -≤+; +≤+) renaming (_≤_ to _≤z_ ; _+_ to _+z_ ; _-_ to _-z_ ; _*_ to _*z_ ; _>_ to _>z_)
open import Data.Product using (_×_ ; proj₁ ; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)

_v↦ᵣ_ : ∀ {ty} → Value ty → Value (MaybeTy→ListTy ty) → Set
IntV xₒ v↦ᵣ IntV xₙ = xₒ ≡ xₙ
NothingV v↦ᵣ NilV = ⊤
JustV vₒ v↦ᵣ ConsV vₙ vₙ₁ = (vₒ v↦ᵣ vₙ) × vₙ₁ ≡ NilV
NilV v↦ᵣ NilV = ⊤
ConsV vₒ vₒ₁ v↦ᵣ ConsV vₙ vₙ₁ = (vₒ v↦ᵣ vₙ) × (vₒ₁ v↦ᵣ vₙ₁)
ClosV {argTy = argTy} {retTy} γₒ bₒ v↦ᵣ ClosV γₙ bₙ = 
    ∀ {argVₒ : Value argTy} {argVₙ : Value (MaybeTy→ListTy argTy)} {argVₒ↦ᵣargV : argVₒ v↦ᵣ argVₙ} 
    {retVₒ : Value retTy} {retVₙ : Value (MaybeTy→ListTy retTy)} → 
    γₒ ,' argVₒ ⊢e bₒ ↓ retVₒ → 
    (γₙ ,' argVₙ) ⊢e bₙ ↓ retVₙ → 
    retVₒ v↦ᵣ retVₙ 
_ v↦ᵣ _ = ⊥

_,_ₑ↦ᵣ_ : ∀ {Γ : Context} → (ext : Extend Γ Under MaybeTy→ListTy) → Env Γ → Env (constructRefContext ext) → Set
eo-root , ∅' ₑ↦ᵣ ∅' = ⊤
eo-elem ext , γₒ ,' vₒ ₑ↦ᵣ (γₙ ,' vₙ) = (ext , γₒ ₑ↦ᵣ γₙ) × (vₒ v↦ᵣ vₙ)
eo-pad x ext , γₒ ₑ↦ᵣ (γₙ ,' v) = ext , γₒ ₑ↦ᵣ γₙ

i+zj≡i₁+zj₁ : ∀ {i j i₁ j₁} → (i≡i₁ : i ≡ i₁) → (j≡j₁ : j ≡ j₁) → i +z j ≡ i₁ +z j₁ 
i+zj≡i₁+zj₁ refl refl = refl

i-zj≡i₁-zj₁ : ∀ {i j i₁ j₁} → (i≡i₁ : i ≡ i₁) → (j≡j₁ : j ≡ j₁) → i -z j ≡ i₁ -z j₁ 
i-zj≡i₁-zj₁ refl refl = refl

i*zj≡i₁*zj₁ : ∀ {i j i₁ j₁} → (i≡i₁ : i ≡ i₁) → (j≡j₁ : j ≡ j₁) → i *z j ≡ i₁ *z j₁ 
i*zj≡i₁*zj₁ refl refl = refl

↓var↦ᵣ↓var : ∀ {Γ ty} → (ext : Extend Γ Under MaybeTy→ListTy) → {γ₁ : Env Γ} {γ₂ : Env (constructRefContext ext)} → (x : Γ ∋ ty) → (ext , γ₁ ₑ↦ᵣ γ₂) → v-lookup γ₁ x v↦ᵣ v-lookup γ₂ (update∋PostRef ext x)
↓var↦ᵣ↓var (eo-elem ext) {γ₁ ,' v} {γ₂ ,' v₁} Z p = proj₂ p
↓var↦ᵣ↓var (eo-elem ext) {γ₁ ,' v} {γ₂ ,' v₁} (S l) p = ↓var↦ᵣ↓var ext l (proj₁ p)
↓var↦ᵣ↓var (eo-pad x ext) {γ₁ ,' v} {γ₂ ,' v₁} l p = ↓var↦ᵣ↓var ext l p

proofJh : ∀ {Γ ty v₁ v₂} → {e : Γ ⊢ ty}
    → (ext : Extend Γ Under MaybeTy→ListTy)
    → {γ₁ : Env Γ} {γ₂ : Env (constructRefContext ext)}
    → γ₁ ⊢e e ↓ v₁
    → γ₂ ⊢e refactorListJH e ext ↓ v₂
    → ext , γ₁ ₑ↦ᵣ γ₂
    → v₁ v↦ᵣ v₂
proofJh ext (↓var x) (↓var .(update∋PostRef ext x)) eq = ↓var↦ᵣ↓var ext x eq
proofJh ext ↓ƛ ↓ƛ eq {argVₒ↦ᵣargV = argVₒ↦ᵣargV} ↓bₒ ↓bₙ = proofJh (eo-elem ext) ↓bₒ ↓bₙ ⟨ eq , argVₒ↦ᵣargV ⟩
proofJh ext (↓· ↓ƛₒ ↓aₒ ↓rₒ) (↓· ↓ƛₙ ↓aₙ ↓rₙ) eq = (proofJh ext ↓ƛₒ ↓ƛₙ eq) {argVₒ↦ᵣargV = proofJh ext ↓aₒ ↓aₙ eq} ↓rₒ ↓rₙ
proofJh ext ↓Int ↓Int eq = refl
proofJh ext (↓+ lₒ rₒ) (↓+ lₙ rₙ) eq = i+zj≡i₁+zj₁ (proofJh ext lₒ lₙ eq) (proofJh ext rₒ rₙ eq)
proofJh ext (↓- lₒ rₒ) (↓- lₙ rₙ) eq = i-zj≡i₁-zj₁ (proofJh ext lₒ lₙ eq) (proofJh ext rₒ rₙ eq)
proofJh ext (↓* lₒ rₒ) (↓* lₙ rₙ) eq = i*zj≡i₁*zj₁ (proofJh ext lₒ lₙ eq) (proofJh ext rₒ rₙ eq)
proofJh ext ↓Nothing ↓[] eq = tt
proofJh ext (↓Just v) (↓:: h ↓[]) eq = ⟨ proofJh ext v h eq , refl ⟩ 
proofJh ext ↓[] ↓[] eq = tt
proofJh ext (↓:: hₒ tₒ) (↓:: hₙ tₙ) eq = ⟨ proofJh ext hₒ hₙ eq , proofJh ext tₒ tₙ eq ⟩
proofJh ext (↓caseMJ mₒ jC) (↓caseL:: mₙ ::C) eq = proofJh (eo-pad (ListTy _) (eo-elem ext)) jC ::C ⟨ eq , proj₁ (proofJh ext mₒ mₙ eq) ⟩
proofJh ext (↓caseMN d₁ d₂) (↓caseL[] d₃ d₄) eq = proofJh ext d₂ d₄ eq
proofJh ext (↓caseL:: d₁ d₂) (↓caseL:: d₃ d₄) eq = proofJh (eo-elem (eo-elem ext)) d₂ d₄ ⟨ ⟨ eq , proj₁ p ⟩ , proj₂ p ⟩
    where
        p = proofJh ext d₁ d₃ eq
proofJh ext (↓caseL[] d₁ d₂) (↓caseL[] d₃ d₄) eq = proofJh ext d₂ d₄ eq
-- absurd cases
proofJh ext (↓caseL[] d₁ d₂) (↓caseL:: d₃ d₄) eq = ⊥-elim (proofJh ext d₁ d₃ eq)
proofJh ext (↓caseL:: d₁ d₂) (↓caseL[] d₃ d₄) eq = ⊥-elim (proofJh ext d₁ d₃ eq)
proofJh ext (↓caseMN d₁ d₂) (↓caseL:: d₃ d₄) eq = ⊥-elim (proofJh ext d₁ d₃ eq)
proofJh ext (↓caseMJ d₁ d₂) (↓caseL[] d₃ d₄) eq = ⊥-elim (proofJh ext d₁ d₃ eq)

proofJ : ∀ {ty v₁ v₂} → {e : ∅ ⊢ ty}
    → (ext : Extend ∅ Under MaybeTy→ListTy)
    → {γ₁ : Env ∅} {γ₂ : Env (constructRefContext ext)}
    → γ₁ ⊢e e ↓ v₁
    → γ₂ ⊢e refactorListJH e ext ↓ v₂
    → ext , γ₁ ₑ↦ᵣ γ₂
    → v₁ v↦ᵣ v₂
proofJ  = proofJh