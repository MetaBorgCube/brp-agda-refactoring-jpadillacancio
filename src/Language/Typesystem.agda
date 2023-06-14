module Typesystem where

open import Data.Integer using (ℤ) -- renaming (Int to ℤ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary.Decidable using (True; toWitness)

{-

src: https://plfa.github.io/DeBruijn/ 

-}

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ
-- infix  5 μ_
infixl 7 _·_
-- infix  8 `suc_
-- infix  9 `_
infix  9 S_
-- infix  9 #_


data Pattern : Set where
    varPattern : Pattern
    
    IntPattern : Pattern
    
    JustPattern : Pattern
    NothingPattern : Pattern

    ::Pattern : Pattern 
    []Pattern : Pattern

    LeftPattern : Pattern
    RightPattern : Pattern

data Type : Set where
    -- Base types
    IntTy : Type
    -- Parametric types 
    _⇒_ : Type → Type → Type
    MaybeTy : Type → Type
    ListTy : Type → Type
    EitherTy : Type → Type → Type  
    
    PatternTy : Pattern → Type

data Context : ℕ → Set where
    ∅ : Context 0
    _,_ : {n : ℕ} → Context n → Type → Context (suc n)

data _∋_ : {n : ℕ} → Context n → Type → Set where

  Z : ∀ {A} {n : ℕ} {Γ : Context n}
      ---------  Γ , A ∋ A
    →  Γ , A ∋ A

  S_ : ∀ {A B} {n : ℕ} {Γ : Context n}
    → Γ ∋ A
      ---------  Γ , B ∋ A
    →  Γ , B ∋ A

data _⊢_ : {n : ℕ} → Context n → Type → Set where
    var :  ∀ {A n} {Γ : Context n}
        → Γ ∋ A
        -----
        → Γ ⊢ A 
    
    -- Add fixpoints or try to integrate them with lambdas
    ƛ  : ∀ {A B n} {Γ : Context n}
        →  Γ , A ⊢ B
        ---------
        → Γ ⊢ A ⇒ B 

    _·_ : ∀ {A B n} {Γ : Context n}
        → Γ ⊢ A ⇒ B
        → Γ ⊢ A
        ---------
        → Γ ⊢ B

    -- Int and Int operations
    Int_ : ∀ {n} {Γ : Context n}
        → ℤ
        → Γ ⊢ IntTy
    _+_ : ∀ {n} {Γ : Context n}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
    _-_ : ∀ {n} {Γ : Context n}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
    _*_ : ∀ {n} {Γ : Context n}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy


    -- MaybeTy
    Nothing : ∀ {A n} {Γ : Context n}
        → Γ ⊢ MaybeTy A
    Just : ∀ {A n} {Γ : Context n}
        → Γ ⊢ A
        → Γ ⊢ MaybeTy A

    -- ListTy
    [] :  ∀ {A n} {Γ : Context n}
        → Γ ⊢ ListTy A
    _::_ : ∀ {A n} {Γ : Context n}
        → Γ ⊢ A
        → Γ ⊢ ListTy A
        → Γ ⊢ ListTy A
      
    -- EitherTy
    Left : ∀ {A B n} {Γ : Context n}
        → Γ ⊢ A
        → Γ ⊢ EitherTy A B
    Right : ∀ {A B n} {Γ : Context n}
        → Γ ⊢ A
        → Γ ⊢ EitherTy A B

    -- For now only support pattern matching on ListTy/EitherTy/MaybeTy
    -- Consider extending pattern matching to be on a type similar to an association ListTy
    caseM_of_to_or_to_ : ∀ {A B n} {Γ : Context n}    
        -- thing ur matching on
        → Γ ⊢ MaybeTy A
        -- case Nothing
        → Γ ⊢ PatternTy NothingPattern
        → Γ ⊢ B
        -- case Just x
        → Γ ⊢ PatternTy JustPattern
        →  Γ , A ⊢ B
        -- Result
        → Γ ⊢ B

    caseL_of_to_or_to_ : ∀ {A B n} {Γ : Context n}    
        -- thing ur matching on
        → Γ ⊢ ListTy A
        -- case []
        → Γ ⊢ PatternTy []Pattern
        → Γ ⊢ B
        -- case x :: xs
        → Γ ⊢ PatternTy ::Pattern
        →  Γ , A , ListTy A ⊢ B
        -- Result
        → Γ ⊢ B

    -- Pattern Terms
    JustP :  ∀ {n} {Γ : Context n}
        → Γ ⊢ PatternTy JustPattern  
    NothingP : ∀ {n} {Γ : Context n}
        → Γ ⊢ PatternTy NothingPattern
    ::P : ∀ {n} {Γ : Context n}
        → Γ ⊢ PatternTy ::Pattern
    []P : ∀ {n} {Γ : Context n}
        → Γ ⊢ PatternTy []Pattern 
    {-
    
    
    caseE_of_to_or_to_ : ∀ {Γ C A B}    
        -- thing ur matching on
        → Γ ⊢ EitherTy A B
        -- case Left
        → Γ ⊢ EitherTy A B 
        → Γ , A ⊢ C
        -- case Right
        → Γ ⊢ EitherTy A B
        → Γ , B ⊢ C
        -- Result
        → Γ ⊢ C
    -}

length : {n : ℕ} → Context n → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {l : ℕ} {Γ : Context l} → {n : ℕ} → (p : n < length Γ) → Type
lookup {Γ = (_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {Γ = (Γ , _)} {(suc n)} (s≤s p)    =  lookup p

{-
count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  var (count (toWitness n∈Γ))   
-}