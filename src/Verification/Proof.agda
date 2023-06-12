module Proof where

open import Typesystem
open import Semantics
open import Refactor using (refactorList ; refactorListH ; update∋PostMap ; mapContext ; MaybeTy→ListTy ; insertIgnoredType ; insertTypeAtIdx)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)  
open import Data.Nat using (ℕ; zero; suc; _<_; _>_ ; _≤_; _≥_; z≤n; s≤s ; _>?_) renaming (_+_ to _+ₙ_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import Data.Integer using (ℤ; -≤-; -≤+; +≤+) renaming (_≤_ to _≤z_ ; _+_ to _+z_ ; _-_ to _-z_ ; _*_ to _*z_)
open import Data.Product using (_×_ ; proj₁ ; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤)

-- {-# TERMINATING #-}
updateEnv : {n : ℕ} {Γ : Context n} → Env Γ → Env (mapContext Γ MaybeTy→ListTy)

updateValue : ∀ {n} {Γ : Context n} {γ : Env Γ} {ty : Type} → (v : Value ty) → Value (MaybeTy→ListTy ty)
updateValue NothingV = NilV
updateValue {γ = γ} (JustV v) = ConsV (updateValue {γ = γ} v) NilV
updateValue (IntV x) = IntV x
updateValue NilV = NilV
updateValue {γ = γ} (ConsV v v₁) = ConsV (updateValue {γ = γ} v) (updateValue {γ = γ} v₁)
updateValue {γ = γ} (LeftV v) = LeftV (updateValue {γ = γ} v)
updateValue {γ = γ} (RightV v) = RightV (updateValue {γ = γ} v)
updateValue (ClosV {n} {Γ} γ body) = ClosV (updateEnv γ) (refactorListH body) 

updateEnv γ = {!   !}

_≡vᵣ_ : ∀ {ty} → Value ty → Value (MaybeTy→ListTy ty) → Set
IntV xₒ ≡vᵣ IntV xₙ = xₒ ≡ xₙ
NothingV ≡vᵣ NilV = ⊤
JustV vₒ ≡vᵣ ConsV vₙ vₙ₁ = (vₒ ≡vᵣ vₙ) × vₙ₁ ≡ NilV
NilV ≡vᵣ NilV = ⊤
ConsV vₒ vₒ₁ ≡vᵣ ConsV vₙ vₙ₁ = (vₒ ≡vᵣ vₙ) × (vₒ₁ ≡vᵣ vₙ₁)
LeftV vₒ ≡vᵣ LeftV vₙ = vₒ ≡vᵣ vₙ
RightV vₒ ≡vᵣ RightV vₙ = vₒ ≡vᵣ vₙ
ClosV {argTy = argTy} {retTy} γₒ bₒ ≡vᵣ ClosV γₙ bₙ = 
    ∀ {argVₒ : Value argTy} {argVₙ : Value (MaybeTy→ListTy argTy)} {argVₒ≡vᵣargV : argVₒ ≡vᵣ argVₙ} 
    {retVₒ : Value retTy} {retVₙ : Value (MaybeTy→ListTy retTy)} → 
    γₒ ,' argVₒ ⊢e bₒ ↓ retVₒ → 
    (γₙ ,' argVₙ) ⊢e bₙ ↓ retVₙ → 
    retVₒ ≡vᵣ retVₙ 
_ ≡vᵣ _ = ⊥

_≡vₚᵣₑ_ : ∀ {ty} → Value ty → Value ty → Set
IntV x ≡vₚᵣₑ IntV x₁ = x ≡ x₁
NothingV ≡vₚᵣₑ NothingV = ⊤
JustV l ≡vₚᵣₑ JustV r = l ≡vₚᵣₑ r
NilV ≡vₚᵣₑ NilV = ⊤
ConsV l l₁ ≡vₚᵣₑ ConsV r r₁ = (l ≡vₚᵣₑ r) × (l₁ ≡vₚᵣₑ r₁)
LeftV l ≡vₚᵣₑ LeftV r = l ≡vₚᵣₑ r
RightV l ≡vₚᵣₑ RightV r = l ≡vₚᵣₑ r
ClosV {argTy = argTy} {retTy} γₗ bₗ ≡vₚᵣₑ ClosV γᵣ bᵣ = ∀ {argVₗ : Value argTy} {argVᵣ : Value argTy} {argVₗ≡vₚᵣₑargVᵣ : argVₗ ≡vₚᵣₑ argVᵣ} 
    {retVₗ : Value retTy} {retVᵣ : Value retTy} → 
    γₗ ,' argVₗ ⊢e bₗ ↓ retVₗ → 
    (γᵣ ,' argVᵣ) ⊢e bᵣ ↓ retVᵣ → 
    retVₗ ≡vₚᵣₑ retVᵣ
_ ≡vₚᵣₑ _ = ⊥

_≡eᵣ_ : ∀ {l} {Γ : Context l} → Env Γ → Env (mapContext Γ MaybeTy→ListTy) → Set
∅' ≡eᵣ ∅' = ⊤
(γₒ ,' v) ≡eᵣ (γₙ ,' v₁) = (γₒ ≡eᵣ γₙ) × (v ≡vᵣ v₁)

insertValAtIdx : ∀ {l ty} {Γ : Context l} → (γ : Env Γ) → (n : ℕ) → {p : n ≤ l} → (ignoreVal : Value ty) → Env (insertTypeAtIdx Γ n p ty)
insertValAtIdx γ zero v = γ ,' v
insertValAtIdx {Γ = Γ , x} γ (suc n) {s≤s p} v = insertValAtIdx ({!   !}) n v ,' {!   !}  

_-ₙ_ : (n : ℕ) → (m : ℕ) → {p : m ≤ n} → ℕ
a -ₙ zero = a
(suc a -ₙ suc b) {s≤s p} = _-ₙ_ a b {p}

<→≤ : ∀ {n m} → (p : n < m) → n ≤ m
<→≤ (s≤s z≤n) = z≤n
<→≤ (s≤s (s≤s p)) = s≤s (<→≤ (s≤s p))

1≤Δ : ∀ {n m} → (p : n > m) → 1 ≤ (_-ₙ_ n m {<→≤ p}) 
1≤Δ (s≤s z≤n) = s≤s z≤n
1≤Δ (s≤s (s≤s p)) = 1≤Δ (s≤s p)

<trans : ∀ {a b c} → (p₁ : a < b) → (p₂ : b < c) → a < c
<trans (s≤s z≤n) (s≤s (s≤s q)) = s≤s z≤n
<trans (s≤s (s≤s p)) (s≤s (s≤s q)) = s≤s (<trans (s≤s p) (s≤s q))

≤trans : ∀ {a b c} → (p₁ : a ≤ b) → (p₂ : b ≤ c) → a ≤ c
≤trans z≤n q = z≤n
≤trans (s≤s m≤n₁) (s≤s m≤n) = s≤s (≤trans m≤n₁ m≤n)

getClosIdx : (l : ℕ) → (lc : ℕ) → {l>0 : l > 0} → {lc<l : lc < l} → ℕ
getClosIdx l lc {l>0} {lc<l}  = _-ₙ_ (_-ₙ_ l lc {<→≤ lc<l}) 1 {1≤Δ lc<l}

-ₙ>0 : ∀ {n m} → (p : n > m) → _-ₙ_ n m {<→≤ p} > 0
-ₙ>0 (s≤s z≤n) = s≤s z≤n
-ₙ>0 (s≤s (s≤s p)) = -ₙ>0 (s≤s p)

≤-reflexive : ∀ {n} → n ≤ n
≤-reflexive {zero} = z≤n
≤-reflexive {suc n} = s≤s ≤-reflexive


n-1<n : ∀ {n} → {n≥1 : n ≥ 1} → _-ₙ_ n 1 {n≥1} < n
n-1<n {_} {s≤s {_} {zero} m≤n} = s≤s z≤n
n-1<n {_} {s≤s {_} {suc n} z≤n} = s≤s (n-1<n {suc n} {s≤s z≤n})

sucn-1≤n : ∀ {n} → ( _-ₙ_ (suc n) 1 {s≤s z≤n}) ≤ n
sucn-1≤n {n} = ≤-reflexive

1-1≤0 : _-ₙ_ 1 1 {s≤s z≤n} ≤ 0
1-1≤0 = z≤n 

n-m<n : ∀ {n m} → (m>0 : m > 0) → {n≥m : n ≥ m } → _-ₙ_ n m {n≥m} < n
n-m<n = {!   !}

n-m≤n : ∀ {n m} → {n≥m : n ≥ m } → _-ₙ_ n m {n≥m} ≤ n
n-m≤n = {!   !}

suca≤b→a<b : ∀ {a b} → suc a ≤ b  → a < b 
suca≤b→a<b p = p

a<b→suca≤b : ∀ {a b} → a < b → suc a ≤ b 
a<b→suca≤b p = p

≤z→≤ₙ : ∀ {a b} → ℤ.pos a ≤z ℤ.pos b → a ≤ b
≤z→≤ₙ (+≤+ m≤n) = m≤n

a≤a+b : ∀ {a b} → a ≤ (a +ₙ b)
a≤a+b {zero} = z≤n
a≤a+b {suc n} = s≤s a≤a+b

a≤b+a : ∀ {a b} → a ≤ (b +ₙ a)
a≤b+a {zero} {b} = z≤n
a≤b+a {suc a} {zero} = s≤s a≤b+a
a≤b+a {suc a} {suc b} = s≤s {!   !}


a≤b→suca≤b : ∀ {a b} → a ≤ b → suc a ≤ b
a≤b→suca≤b z≤n = {!   !}
a≤b→suca≤b (s≤s p) = {!   !}

a-b≤c→a≤c+b : ∀ {a b c} → {p : b ≤ a} → _-ₙ_ a b {p} ≤ c → a ≤ c +ₙ b
a-b≤c→a≤c+b {_} {zero} {zero} a-b≤c = a-b≤c
a-b≤c→a≤c+b {_} {zero} {suc n} z≤n = z≤n
a-b≤c→a≤c+b {_} {zero} {suc n} (s≤s m≤n) = s≤s (a-b≤c→a≤c+b m≤n)
a-b≤c→a≤c+b {_} {suc b} {zero} {s≤s m≤n} a-b≤c = s≤s (a-b≤c→a≤c+b a-b≤c)
a-b≤c→a≤c+b {suc a} {suc b} {suc c} {s≤s p} a-b≤c = s≤s (a-b≤c→a≤c+b {a} {suc b} {c} {{! a≤b→suca≤b ?  !}} {!   !})

a≤c+b→a-b≤c : ∀ {a b c} → {p : b ≤ a} → a ≤ c +ₙ b → _-ₙ_ a b {p} ≤ c
a≤c+b→a-b≤c {zero} {p = z≤n} a≤c+b = z≤n
a≤c+b→a-b≤c {suc a} {p = z≤n} a≤c+b = {!    !}
a≤c+b→a-b≤c {p = s≤s p} a≤c+b = {! -c   !}

a≤b→a≤c : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c 
a≤b→a≤c a≤b refl = a≤b

insertIgnoredValClos : ∀ {l aTy rTy iTy} {l>0 : l > 0} {Γ : Context l} {γ : Env Γ} {l-clos} {l-clos<l : l-clos < l } {Γ-clos : Context l-clos} {γ-clos : Env Γ-clos} → 
    -- ignored value
    {iVal : Value iTy} → 
    -- closure value
    (v : Value (aTy ⇒ rTy)) →
    -- ensure that γ-clos corresponds to our value
    {e : Γ ⊢ (aTy ⇒ rTy)} →
    {γ⊢e↓v : γ ⊢e e ↓ v} →
    {body : Γ-clos , aTy ⊢ rTy}
    {v≡ClosV : v ≡ ClosV γ-clos body} → 
    -- index to ignore in env
    {idx : ℕ} →
    {idx≤l : idx ≤ l} →
    -- Proof if index > C_p or not 
    Dec (idx > getClosIdx l l-clos {l>0} {l-clos<l})  → 
    Value (aTy ⇒ rTy) 
insertIgnoredValClos {l = l} {iTy = iTy} {l>0 = l>0} {l-clos = l-clos} {l-clos<l = l-clos<l} {iVal = iVal} (ClosV nv b) {v≡ClosV = refl} {idx = idx} {idx≤l = idx≤l} (yes idx>Cₚ) = 
    -- idx - Cₚ - 1 = idx - l + l-clos 
    ClosV 
        (insertValAtIdx 
            {l = l-clos}
            nv 
            idx-clos
            {idx-clos≤l-clos}
            iVal
        ) 
        (insertIgnoredType b {suc idx-clos} {s≤s idx-clos≤l-clos} {iTy})
    where
        Cₚ = getClosIdx l l-clos {l>0} {l-clos<l}
        idx-Cₚ = _-ₙ_ 
                    idx 
                    Cₚ 
                    {<→≤ idx>Cₚ}
                
        idx-clos = (_-ₙ_ 
                idx-Cₚ
                1 
                {1≤Δ idx>Cₚ}
            )
        idx-clos≤l-clos : idx-clos ≤ l-clos
        idx-clos≤l-clos = 
            a≤c+b→a-b≤c 
            {idx-Cₚ} 
            {1} 
            {l-clos} 
            {1≤Δ idx>Cₚ} 
            (a≤c+b→a-b≤c 
                {idx} {Cₚ} {l-clos +ₙ 1} {<→≤ idx>Cₚ} (a≤b→a≤c idx≤l {!   !})
            )

insertIgnoredValClos v (no ¬idx>Cₚ) = v

-- this approach is wrong because it can also evaluate to a closure through a var (as such closure env != expr env) 
-- so need to do some number fuckery with n-l or whatev
insertIgnoredValVal : ∀ {l eTy iTy} {Γ : Context l} {γ : Env Γ} {e : Γ ⊢ eTy} → (v : Value eTy) → {d : γ ⊢e e ↓ v} → {n : ℕ} → {p : n ≤ l} → Value iTy → Value eTy
insertIgnoredValVal {l} {γ = γ} (ClosV γ-clos body) {d} {n} {p} iVal = insertIgnoredValClos (ClosV γ-clos body) {!   !}
insertIgnoredValVal (IntV x) iVal = IntV x
insertIgnoredValVal NothingV iVal = NothingV
insertIgnoredValVal (JustV v) iVal = JustV (insertIgnoredValVal v iVal)
insertIgnoredValVal NilV iVal = NilV
insertIgnoredValVal (ConsV h t) iVal = ConsV (insertIgnoredValVal h iVal) (insertIgnoredValVal t iVal)
insertIgnoredValVal (LeftV v) iVal = LeftV (insertIgnoredValVal v iVal)
insertIgnoredValVal (RightV v) iVal = RightV (insertIgnoredValVal v iVal)

insertIgnoredVal : ∀ {l eTy iTy} {Γ : Context l} {e : Γ ⊢ eTy} {v : Value eTy} {γ : Env Γ} 
    → (d : γ ⊢e e ↓ v) 
    → {n : ℕ} 
    → {p : n ≤ l} 
    → {iVal : Value iTy} 
    → insertValAtIdx γ n {p} iVal ⊢e insertIgnoredType e ↓ insertIgnoredValVal {Γ = Γ} {γ = γ} {e = e} v {d = d} {p = p} iVal
insertIgnoredVal = {!   !}

i+zj≡i₁+zj₁ : ∀ {i j i₁ j₁} → (i≡i₁ : i ≡ i₁) → (j≡j₁ : j ≡ j₁) → i +z j ≡ i₁ +z j₁ 
i+zj≡i₁+zj₁ {ℤ.pos n} refl refl = refl
i+zj≡i₁+zj₁ {ℤ.negsuc n} refl refl = refl

i-zj≡i₁-zj₁ : ∀ {i j i₁ j₁} → (i≡i₁ : i ≡ i₁) → (j≡j₁ : j ≡ j₁) → i -z j ≡ i₁ -z j₁ 
i-zj≡i₁-zj₁ {ℤ.pos n} refl refl = refl
i-zj≡i₁-zj₁ {ℤ.negsuc n} refl refl = refl

i*zj≡i₁*zj₁ : ∀ {i j i₁ j₁} → (i≡i₁ : i ≡ i₁) → (j≡j₁ : j ≡ j₁) → i *z j ≡ i₁ *z j₁ 
i*zj≡i₁*zj₁ {ℤ.pos n} refl refl = refl
i*zj≡i₁*zj₁ {ℤ.negsuc n} refl refl = refl 

v-lookupγₒx≡vᵣv-lookupγₙxₙ : 
    ∀ {ty l} {Γ : Context l} → 
    (γₒ : Env Γ) → (x : Γ ∋ ty) → 
    (γₙ : Env (mapContext Γ MaybeTy→ListTy)) → 
    (γₒ≡eᵣγₙ : γₒ ≡eᵣ γₙ) →
    v-lookup γₒ x ≡vᵣ v-lookup γₙ (Refactor.update∋PostMap x)
v-lookupγₒx≡vᵣv-lookupγₙxₙ (γₒ ,' v) Z (γₙ ,' v₁) ⟨ _ , v≡vᵣv₁ ⟩ = v≡vᵣv₁
v-lookupγₒx≡vᵣv-lookupγₙxₙ (γₒ ,' v) (S x) (γₙ ,' v₁) ⟨ γₒ≡eᵣγₙ , _ ⟩ = v-lookupγₒx≡vᵣv-lookupγₙxₙ γₒ x γₙ γₒ≡eᵣγₙ

-- trans rights :D
≡vᵣ-trans : ∀ {ty} {v₀ : Value ty} {v₁ v₂ : Value (MaybeTy→ListTy ty)} → 
    {_ : MaybeTy→ListTy ty ≡ MaybeTy→ListTy (MaybeTy→ListTy ty)} → 
    v₀ ≡vᵣ v₁ → 
    {! v₁ ≡vᵣ v₂ →
    ?  !} --   v₀ ≡vᵣ v₂
≡vᵣ-trans = {!   !}

≡vₚᵣₑ×≡vᵣ→≡vᵣ : ∀ {ty} {lₒ lₙ : Value ty} {r : Value (MaybeTy→ListTy ty)} → lₒ ≡vₚᵣₑ lₙ → lₙ ≡vᵣ r → lₒ ≡vᵣ r
≡vₚᵣₑ×≡vᵣ→≡vᵣ {ty} lₒ≡vₚᵣₑlₙ lₙ≡vᵣr = {!   !}



verifySemanticEqH : 
    ∀ {l ty} {Γ : Context l} {γₒ : Env Γ} {vₒ : Value ty} {vₙ : Value (MaybeTy→ListTy ty)}  {e : Γ ⊢ ty} → 
    γₒ ⊢e e ↓ vₒ →  
    (γₙ : Env (mapContext Γ MaybeTy→ListTy)) → 
    (γₒ≡eᵣγₙ : γₒ ≡eᵣ γₙ) → 
    γₙ ⊢e refactorListH e ↓ vₙ → 
    vₒ ≡vᵣ vₙ
{-
insertionProofConversion : ∀ {} → 
     (γ ,' iVal) ⊢e insertIgnoredType (refactorListH justClause) ↓ vₙ →
     (γ) ⊢e refactorListH justClause ↓ vₙ
insertionProofConversion = {!   !}
-}



verifySemanticEqH {γₒ = γₒ} (↓var x) γₙ γₒ≡eᵣγₙ (↓var .(update∋PostMap x)) = 
    v-lookupγₒx≡vᵣv-lookupγₙxₙ γₒ x γₙ γₒ≡eᵣγₙ
verifySemanticEqH ↓ƛ γₙ γₒ≡eᵣγₙ ↓ƛ {argVₙ = argVₙ} {argVₒ≡vᵣargV} ↓clₒ ↓clₙ = 
    verifySemanticEqH ↓clₒ (γₙ ,' argVₙ) ⟨ γₒ≡eᵣγₙ , argVₒ≡vᵣargV ⟩ ↓clₙ 
verifySemanticEqH (↓· ↓ƛₒ ↓aₒ ↓rₒ) γₙ γₒ≡eᵣγₙ (↓· ↓ƛₙ ↓aₙ ↓rₙ) =  
    (verifySemanticEqH ↓ƛₒ γₙ γₒ≡eᵣγₙ ↓ƛₙ) {argVₒ≡vᵣargV = verifySemanticEqH ↓aₒ γₙ γₒ≡eᵣγₙ ↓aₙ} ↓rₒ ↓rₙ
-- Integer related proofs
verifySemanticEqH ↓Int γₙ γₒ≡eᵣγₙ ↓Int = refl
verifySemanticEqH (↓+ dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓+ dₙ dₙ₁) = 
    i+zj≡i₁+zj₁ (verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ) (verifySemanticEqH dₒ₁ γₙ γₒ≡eᵣγₙ dₙ₁)
verifySemanticEqH (↓- dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓- dₙ dₙ₁) = 
    i-zj≡i₁-zj₁ (verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ) (verifySemanticEqH dₒ₁ γₙ γₒ≡eᵣγₙ dₙ₁)
verifySemanticEqH (↓* dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓* dₙ dₙ₁) = 
    i*zj≡i₁*zj₁ (verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ) (verifySemanticEqH dₒ₁ γₙ γₒ≡eᵣγₙ dₙ₁)
-- Maybe
verifySemanticEqH ↓Nothing γₙ γₒ≡eᵣγₙ ↓[] = ⊤.tt
verifySemanticEqH (↓Just dₒ) γₙ γₒ≡eᵣγₙ (↓:: dₙ ↓[]) = ⟨ verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ , refl ⟩ 
-- List
verifySemanticEqH ↓[] γₙ γₒ≡eᵣγₙ ↓[] = ⊤.tt
verifySemanticEqH (↓:: dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓:: dₙ dₙ₁) = ⟨ verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ , verifySemanticEqH dₒ₁ γₙ γₒ≡eᵣγₙ dₙ₁ ⟩
-- Either
verifySemanticEqH (↓Left dₒ) γₙ γₒ≡eᵣγₙ (↓Left dₙ) = verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ
verifySemanticEqH (↓Right dₒ) γₙ γₒ≡eᵣγₙ (↓Right dₙ) = verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ
-- case statements
verifySemanticEqH {e = e} (↓caseMJ dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓caseL:: {hVal = hVal} {tVal} dₙ dₙ₁) =  
    ≡vₚᵣₑ×≡vᵣ→≡vᵣ {!   !} (verifySemanticEqH (insertIgnoredVal dₒ₁) (insertValAtIdx (γₙ ,' {!   !}) 0 {!   !}) {!   !} {!  dₙ₁ !})
    -- verifySemanticEqH dₒ₁ (γₙ ,' hVal) ⟨ γₒ≡eᵣγₙ , proj₁ (verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ) ⟩ {! dₙ₁  !}
verifySemanticEqH (↓caseMN dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓caseL[] dₙ dₙ₁) = verifySemanticEqH dₒ₁ γₙ γₒ≡eᵣγₙ dₙ₁
verifySemanticEqH (↓caseL:: {hVal = hValₒ} {tValₒ} dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓caseL:: {hVal = hValₙ} {tValₙ} dₙ dₙ₁) = 
    verifySemanticEqH dₒ₁ ((γₙ ,' hValₙ) ,' tValₙ) ⟨ ⟨ γₒ≡eᵣγₙ , proj₁ hValₒ≡hValₙ×tValₒ≡tValₙ ⟩ , proj₂ hValₒ≡hValₙ×tValₒ≡tValₙ ⟩ dₙ₁ 
    where 
        hValₒ≡hValₙ×tValₒ≡tValₙ = verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ
verifySemanticEqH (↓caseL[] dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓caseL[] dₙ dₙ₁) = verifySemanticEqH dₒ₁ γₙ γₒ≡eᵣγₙ dₙ₁
-- absurd case statements
verifySemanticEqH (↓caseL:: {hVal = hValₒ} {tValₒ}  dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓caseL[] dₙ dₙ₁) =  ⊥-elim (verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ) 
verifySemanticEqH (↓caseL[] dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓caseL:: dₙ dₙ₁) = ⊥-elim (verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ)
verifySemanticEqH (↓caseMJ {val = valₒ} dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓caseL[] dₙ dₙ₁) = ⊥-elim (verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ)
verifySemanticEqH (↓caseMN dₒ dₒ₁) γₙ γₒ≡eᵣγₙ (↓caseL:: dₙ dₙ₁) = ⊥-elim (verifySemanticEqH dₒ γₙ γₒ≡eᵣγₙ dₙ)

verifySemanticEq : ∀  {ty} {vₒ : Value ty} {vₙ : Value (MaybeTy→ListTy ty)} {e : ∅ ⊢ ty} → ∅' ⊢e e ↓ vₒ → ∅' ⊢e refactorList e ↓ vₙ → vₒ ≡vᵣ vₙ
verifySemanticEq dₒ dₙ = verifySemanticEqH dₒ ∅' ⊤.tt dₙ         