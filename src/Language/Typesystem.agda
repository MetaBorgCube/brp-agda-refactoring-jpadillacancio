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
infixl 7 _·_
infix  9 S_


data Pattern : Set where
    varPattern : Pattern
    
    IntPattern : Pattern
    
    JustPattern : Pattern
    NothingPattern : Pattern

    ::Pattern : Pattern 
    []Pattern : Pattern

data Type : Set where
    -- Base types
    IntTy : Type
    -- Parametric types 
    _⇒_ : Type → Type → Type
    MaybeTy : Type → Type
    ListTy : Type → Type
    -- EitherTy : Type → Type → Type  
    
    PatternTy : Pattern → Type

data Context : Set where
    ∅ : Context
    _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {A} {Γ : Context}
      ---------  Γ , A ∋ A
    →  Γ , A ∋ A

  S_ : ∀ {A B} {Γ : Context}
    → Γ ∋ A
      ---------  Γ , B ∋ A
    →  Γ , B ∋ A

data _⊢_ : Context → Type → Set where
    var :  ∀ {A} {Γ : Context}
        → Γ ∋ A
        -----
        → Γ ⊢ A 
    
    -- Add fixpoints or try to integrate them with lambdas
    ƛ  : ∀ {A B} {Γ : Context}
        →  Γ , A ⊢ B
        ---------
        → Γ ⊢ A ⇒ B 

    _·_ : ∀ {A B} {Γ : Context}
        → Γ ⊢ A ⇒ B
        → Γ ⊢ A
        ---------
        → Γ ⊢ B

    -- Int and Int operations
    Int_ : ∀ {Γ : Context}
        → ℤ
        → Γ ⊢ IntTy
    _+_ : ∀ {Γ : Context}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
    _-_ : ∀ {Γ : Context}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
    _*_ : ∀ {Γ : Context}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy


    -- MaybeTy
    Nothing : ∀ {A} {Γ : Context}
        → Γ ⊢ MaybeTy A
    Just : ∀ {A} {Γ : Context}
        → Γ ⊢ A
        → Γ ⊢ MaybeTy A

    -- ListTy
    [] :  ∀ {A} {Γ : Context}
        → Γ ⊢ ListTy A
    _::_ : ∀ {A} {Γ : Context}
        → Γ ⊢ A
        → Γ ⊢ ListTy A
        → Γ ⊢ ListTy A
      
    -- For now only support pattern matching on ListTy/MaybeTy
    -- Consider extending pattern matching to be on a type similar to an association ListTy
    caseM_of_to_or_to_ : ∀ {A B} {Γ : Context}    
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

    caseL_of_to_or_to_ : ∀ {A B} {Γ : Context}    
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
    JustP :  ∀ {Γ : Context}
        → Γ ⊢ PatternTy JustPattern  
    NothingP : ∀ {Γ : Context}
        → Γ ⊢ PatternTy NothingPattern
    ::P : ∀ {Γ : Context}
        → Γ ⊢ PatternTy ::Pattern
    []P : ∀ {Γ : Context}
        → Γ ⊢ PatternTy []Pattern 

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {Γ = (_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {Γ = (Γ , _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  var (count (toWitness n∈Γ))   