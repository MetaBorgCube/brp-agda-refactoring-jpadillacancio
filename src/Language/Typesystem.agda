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
infix  9 #_


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

data Context : Set where
    ∅ : Context
    _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where
    var :  ∀ {Γ A}
        → Γ ∋ A
        -----
        → Γ ⊢ A 
    
    -- Add fixpoints or try to integrate them with lambdas
    ƛ  : ∀ {Γ A B}
        → Γ , A ⊢ B
        ---------
        → Γ ⊢ A ⇒ B 

    _·_ : ∀ {Γ A B}
        → Γ ⊢ A ⇒ B
        → Γ ⊢ A
        ---------
        → Γ ⊢ B
    
    -- Int and Int operations
    -- a wee bit confused if this should take any args
    Int_ : ∀ {Γ}
        → ℤ
        → Γ ⊢ IntTy
    _+_ : ∀ {Γ}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
    _-_ : ∀ {Γ}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
    _*_ : ∀ {Γ}
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy
        → Γ ⊢ IntTy


    -- MaybeTy
    Nothing : ∀ {Γ A}
        → Γ ⊢ MaybeTy A
    Just : ∀ {Γ A}
        → Γ ⊢ A
        → Γ ⊢ MaybeTy A

    -- ListTy
    [] :  ∀ {Γ A}
        → Γ ⊢ ListTy A
    _::_ : ∀ {Γ A}
        → Γ ⊢ A
        → Γ ⊢ ListTy A
        → Γ ⊢ ListTy A
    {-
    head : ∀ {Γ A}
        → Γ ⊢ ListTy A
        → Γ ⊢ A
    tail : ∀ {Γ A}
        → Γ ⊢ ListTy A
        → Γ ⊢ ListTy A
    -}
      
    -- EitherTy
    Left : ∀ {Γ A B}
        → Γ ⊢ A
        → Γ ⊢ EitherTy A B
    Right : ∀ {Γ A B}
        → Γ ⊢ A
        → Γ ⊢ EitherTy A B

    -- For now only support pattern matching on ListTy/EitherTy/MaybeTy
    -- Consider extending pattern matching to be on a type similar to an association ListTy
    caseM_of_to_or_to_ : ∀ {Γ A B}    
        -- thing ur matching on
        → Γ ⊢ MaybeTy A
        -- case Nothing
        → Γ ⊢ PatternTy NothingPattern
        → Γ ⊢ B
        -- case Just x
        → Γ ⊢ PatternTy JustPattern
        → Γ , A ⊢ B
        -- Result
        → Γ ⊢ B

    caseL_of_to_or_to_ : ∀ {Γ A B}    
        -- thing ur matching on
        → Γ ⊢ ListTy A
        -- case []
        → Γ ⊢ PatternTy []Pattern
        → Γ ⊢ B
        -- case x :: xs
        → Γ ⊢ PatternTy ::Pattern
        → Γ , A , ListTy A ⊢ B
        -- Result
        → Γ ⊢ B

    -- Pattern Terms
    JustP :  ∀ {Γ}
        → Γ ⊢ PatternTy JustPattern  
    NothingP : ∀ {Γ}
        → Γ ⊢ PatternTy NothingPattern
    ::P : ∀ {Γ}
        → Γ ⊢ PatternTy ::Pattern
    []P : ∀ {Γ}
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

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  var (count (toWitness n∈Γ))   