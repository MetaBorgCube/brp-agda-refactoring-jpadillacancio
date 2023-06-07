module Proof where

open import Typesystem
open import Semantics
open import Refactor using (refactorList ; refactorListH ; mapContext ; MaybeTy→ListTy ; insertIgnoredType ; insertTypeAtIdx)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)  
open import Data.Nat using (ℕ; zero; suc; _<_; _>_ ; _≤_; _≥_; z≤n; s≤s ; _>?_) renaming (_+_ to _+ₙ_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import Data.Integer using (ℤ; -≤-; -≤+; +≤+) renaming (_≤_ to _≤z_ ; _+_ to _+z_ ; _-_ to _-z_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)


{-# TERMINATING #-}
updateEnv : {n : ℕ} {Γ : Context n} → Env Γ → Env (mapContext Γ MaybeTy→ListTy)

updateValue : ∀ {n} {Γ : Context n} {γ : Env Γ} {ty : Type} {e : Γ ⊢ ty} → (v : Value ty) → {d : γ ⊢e e ↓ v} → Value (MaybeTy→ListTy ty)
updateValue (IntV x) = IntV x
updateValue NothingV = NilV
updateValue {.(suc _)} {.(_ , MaybeTy ty)} {γ} {MaybeTy ty} {var Z} (JustV v) {d} = {! d !}
updateValue {.(suc _)} {.(_ , _)} {γ} {MaybeTy ty} {var (S x)} (JustV v) {d} = {!   !}
updateValue {n} {Γ} {γ} {MaybeTy ty} {e · e₁} (JustV v) {↓· d d₁ d₂} = {!   !}
updateValue {n} {Γ} {γ} {MaybeTy .IntTy} {Just e} (JustV v) {↓Just d} = {!   !}
updateValue {n} {Γ} {γ} {MaybeTy ty} {caseM e of .NothingP to e₂ or .JustP to e₄} (JustV v) {↓caseMJ d d₁} = ConsV (updateValue {Γ = {!   !}} {γ = {!   !}} {e = {! e₄  !}} v {{!   !}}) {!   !}
updateValue {n} {Γ} {γ} {MaybeTy ty} {caseM e of .NothingP to e₂ or .JustP to e₄} (JustV v) {↓caseMN d d₁} = {!   !}
updateValue {n} {Γ} {γ} {MaybeTy ty} {caseL e of .[]P to e₂ or .::P to e₄} (JustV v) {↓caseL:: d d₁} = {!   !}
updateValue {n} {Γ} {γ} {MaybeTy ty} {caseL e of .[]P to e₂ or .::P to e₄} (JustV v) {↓caseL[] d d₁} = {!   !}
updateValue (JustV v) = ConsV (updateValue {{!   !}} {{!   !}} {{!   !}} {{!   !}} {{!   !}} v {{!   !}}) NilV
updateValue NilV = {!   !}
updateValue (ConsV v v₁) = {!   !}
updateValue (LeftV v) = {!   !}
updateValue (RightV v) = {!   !}
updateValue (ClosV x x₁) = {!   !}
{-
updateValue NothingV = NilV
updateValue (JustV v) = ConsV (updateValue v) NilV
updateValue (IntV x) = IntV x
updateValue NilV = NilV
updateValue (ConsV v v₁) = ConsV (updateValue v) (updateValue v₁)
updateValue (LeftV v) = LeftV (updateValue v)
updateValue (RightV v) = RightV (updateValue v)
-- rewrite this so that it takes into account what the expr is that this value was got from
-- in the case that it was got from caseL:: then insert ignored val into env and body
updateValue (ClosV {n} {Γ} γ body) = ClosV (updateEnv γ) (refactorListH body) 

updateEnv {zero} {∅} γ = ∅'
-- construct fake expression that is just a var (so updateValue does not change it)
updateEnv {suc n} {Γ , _} γ = updateEnv {n} {Γ} (λ x →  γ (S x)) ,' updateValue (γ Z)
-}
updateEnv = {!   !}


-- _≡ₑ_ : ∀ {aTy rTy} → Value (aTy ⇒ rTy) → Value (MaybeTy→ListTy aTy ⇒ MaybeTy→ListTy rTy) → Set 

data _≡ᵣ_ : ∀ {ty} → Value ty → Value (MaybeTy→ListTy ty) → Set where
    NothingV≡ᵣNilV : ∀ {v} → NothingV {v} ≡ᵣ NilV
    JustV≡ᵣConsV : ∀ {ty} {vₒ : Value ty} {vₙ} → vₒ ≡ᵣ vₙ  → JustV vₒ ≡ᵣ ConsV vₙ NilV
    NilV≡ᵣNilV : ∀ {ty} {v : Value ty} → NilV {ty} ≡ᵣ NilV
    ConsV≡ᵣConsV : ∀ {ty} {hₒ : Value ty} {tₒ} {hₙ} {tₙ} → hₒ ≡ᵣ hₙ → tₒ ≡ᵣ tₙ → ConsV hₒ tₒ ≡ᵣ ConsV hₙ tₙ
    LeftV≡ᵣLeftV : ∀ {ty₁ ty₂} {vₒ : Value (EitherTy ty₁ ty₂)} {vₙ} → vₒ ≡ᵣ vₙ  → LeftV {B = ty₂} vₒ ≡ᵣ LeftV vₙ
    RightV≡ᵣRightV : ∀ {ty₁ ty₂} {vₒ : Value (EitherTy ty₁ ty₂)} {vₙ} → vₒ ≡ᵣ vₙ  → RightV {A = ty₁} vₒ ≡ᵣ RightV vₙ
    ClosV≡ᵣClosV : ∀ {aTy} {rTy} {γₒ : Env {!   !}} {γₙ : Env {!   !}} { argValₒ : Value aTy} { argValₙ : Value (MaybeTy→ListTy aTy)} {retValₒ : Value rTy} {retValₙ : Value (MaybeTy→ListTy rTy)} {bₒ bₙ} → 
        {!   !}
        -- If arguments are refactor-equivalent
        {argValₒ ≡ᵣ argValₙ} → 
        -- and the function evaluates to the return value given the argument
        {(γₒ ,' argValₒ) ⊢e bₒ ↓ retValₒ} → 
        {(γₙ ,' argValₙ) ⊢e bₙ ↓ retValₙ} →
        -- then the closures are equivalent if the return values are refactor-equivalent 
        retValₒ ≡ᵣ retValₙ
{-
_≡ₑ_ {aTy} {rTy} (ClosV γₒ bₒ) (ClosV γₙ bₙ) = 
    ∀ { argValₒ : Value aTy} { argValₙ : Value (MaybeTy→ListTy aTy)} {retValₒ : Value rTy} {retValₙ : Value (MaybeTy→ListTy rTy)} → 
    -- If arguments are refactor-equivalent
    {argValₒ ≡ᵣ argValₙ} → 
    -- and the function evaluates to the return value given the argument
    {(γₒ ,' argValₒ) ⊢e bₒ ↓ retValₒ} → 
    {(γₙ ,' argValₙ) ⊢e bₙ ↓ retValₙ} →
    -- then the closures are equivalent if the return values are refactor-equivalent 
    retValₒ ≡ᵣ retValₙ
-}
insertValAtIdx : ∀ {l ty} {Γ : Context l} → (γ : Env Γ) → (n : ℕ) → {p : n ≤ l} → (ignoreVal : Value ty) → Env (insertTypeAtIdx Γ n p ty)
insertValAtIdx γ zero v = γ ,' v
insertValAtIdx {Γ = Γ , x} γ (suc n) {s≤s p} v = insertValAtIdx (Env-tail γ) n v ,' Env-head γ  

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

verifySemanticEqH : ∀ {l ty} {Γ : Context l} {γ : Env Γ} {v : Value ty} {e : Γ ⊢ ty} → γ ⊢e e ↓ v →  updateEnv γ ⊢e refactorListH e ↓ {!   !}
verifySemanticEqH = {!   !}
{-
verifySemanticEqH (↓var x) = {!  ↓var !}
verifySemanticEqH ↓ƛ = {!   !}
verifySemanticEqH (↓· p p₁ p₂) = {!   !}
verifySemanticEqH ↓Int = ↓Int
verifySemanticEqH (↓+ p p₁) = ↓+ (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓- p p₁) = ↓- (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓* p p₁) = ↓* (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH ↓Nothing = ↓[]
verifySemanticEqH (↓Just p) = ↓:: (verifySemanticEqH p) ↓[]
verifySemanticEqH ↓[] = ↓[]
verifySemanticEqH (↓:: p p₁) = ↓:: (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓Left p) = ↓Left (verifySemanticEqH p)
verifySemanticEqH (↓Right p) = ↓Right (verifySemanticEqH p)
verifySemanticEqH (↓caseMJ p p₁) = ↓caseL:: (verifySemanticEqH p) (insertIgnoredVal (verifySemanticEqH p₁) {0} {z≤n} {NilV})
verifySemanticEqH (↓caseMN p p₁) = ↓caseL[] (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓caseL:: p p₁) = ↓caseL:: (verifySemanticEqH p) (verifySemanticEqH p₁)
verifySemanticEqH (↓caseL[] p p₁) = ↓caseL[] (verifySemanticEqH p) (verifySemanticEqH p₁)

verifySemanticEq : ∀  {ty} {v : Value ty} {e : ∅ ⊢ ty} → ∅' ⊢e e ↓ v → ∅' ⊢e refactorList e ↓ updateValue v
verifySemanticEq d = verifySemanticEqH d    
-} 