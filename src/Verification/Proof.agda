module Proof where

open import Typesystem
open import Semantics
open import Refactor using (refactorList ; refactorListH  ; MaybeTy→ListTy ; constructRefContext ; Extend_Under_ ; eo-root ; eo-elem ; eo-pad ; update∋PostRef) 
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

proofH : ∀ {Γ ty v₁ v₂} → {e : Γ ⊢ ty}
    → (ext : Extend Γ Under MaybeTy→ListTy)
    → {γ₁ : Env Γ} {γ₂ : Env (constructRefContext ext)}
    → γ₁ ⊢e e ↓ v₁
    → γ₂ ⊢e refactorListH e ext ↓ v₂
    → ext , γ₁ ₑ↦ᵣ γ₂
    → v₁ v↦ᵣ v₂
proofH ext (↓var x) (↓var .(update∋PostRef ext x)) eq = ↓var↦ᵣ↓var ext x eq
proofH ext ↓ƛ ↓ƛ eq {argVₒ↦ᵣargV = argVₒ↦ᵣargV} ↓bₒ ↓bₙ = proofH (eo-elem ext) ↓bₒ ↓bₙ ⟨ eq , argVₒ↦ᵣargV ⟩
proofH ext (↓· ↓ƛₒ ↓aₒ ↓rₒ) (↓· ↓ƛₙ ↓aₙ ↓rₙ) eq = (proofH ext ↓ƛₒ ↓ƛₙ eq) {argVₒ↦ᵣargV = proofH ext ↓aₒ ↓aₙ eq} ↓rₒ ↓rₙ
proofH ext ↓Int ↓Int eq = refl
proofH ext (↓+ lₒ rₒ) (↓+ lₙ rₙ) eq = i+zj≡i₁+zj₁ (proofH ext lₒ lₙ eq) (proofH ext rₒ rₙ eq)
proofH ext (↓- lₒ rₒ) (↓- lₙ rₙ) eq = i-zj≡i₁-zj₁ (proofH ext lₒ lₙ eq) (proofH ext rₒ rₙ eq)
proofH ext (↓* lₒ rₒ) (↓* lₙ rₙ) eq = i*zj≡i₁*zj₁ (proofH ext lₒ lₙ eq) (proofH ext rₒ rₙ eq)
proofH ext ↓Nothing ↓[] eq = tt
proofH ext (↓Just v) (↓:: h ↓[]) eq = ⟨ proofH ext v h eq , refl ⟩ 
proofH ext ↓[] ↓[] eq = tt
proofH ext (↓:: hₒ tₒ) (↓:: hₙ tₙ) eq = ⟨ proofH ext hₒ hₙ eq , proofH ext tₒ tₙ eq ⟩
proofH ext (↓caseMJ mₒ jC) (↓caseL:: mₙ ::C) eq = proofH (eo-pad (ListTy _) (eo-elem ext)) jC ::C ⟨ eq , proj₁ (proofH ext mₒ mₙ eq) ⟩
proofH ext (↓caseMN mₒ nC) (↓caseL[] mₙ []C) eq = proofH ext nC []C eq
proofH ext (↓caseL:: mₒ ::Cₒ) (↓caseL:: mₙ ::Cₙ) eq = proofH (eo-elem (eo-elem ext)) ::Cₒ ::Cₙ ⟨ ⟨ eq , proj₁ hValₒv↦ᵣhValₙ×tValₒv↦ᵣtValₙ ⟩ , proj₂ hValₒv↦ᵣhValₙ×tValₒv↦ᵣtValₙ ⟩
    where
        hValₒv↦ᵣhValₙ×tValₒv↦ᵣtValₙ = proofH ext mₒ mₙ eq
proofH ext (↓caseL[] mₒ []Cₒ) (↓caseL[] mₙ []Cₙ) eq = proofH ext []Cₒ []Cₙ eq
-- absurd cases
proofH ext (↓caseL[] mₒ _) (↓caseL:: mₙ _) eq = ⊥-elim (proofH ext mₒ mₙ eq)
proofH ext (↓caseL:: mₒ _) (↓caseL[] mₙ _) eq = ⊥-elim (proofH ext mₒ mₙ eq)
proofH ext (↓caseMN mₒ _) (↓caseL:: mₙ _) eq = ⊥-elim (proofH ext mₒ mₙ eq)
proofH ext (↓caseMJ mₒ _) (↓caseL[] mₙ _) eq = ⊥-elim (proofH ext mₒ mₙ eq)

proof : ∀ {ty v₁ v₂} → {e : ∅ ⊢ ty}
    → (ext : Extend ∅ Under MaybeTy→ListTy)
    → {γ₁ : Env ∅} {γ₂ : Env (constructRefContext ext)}
    → γ₁ ⊢e e ↓ v₁
    → γ₂ ⊢e refactorListH e ext ↓ v₂
    → ext , γ₁ ₑ↦ᵣ γ₂
    → v₁ v↦ᵣ v₂
proof  = proofH