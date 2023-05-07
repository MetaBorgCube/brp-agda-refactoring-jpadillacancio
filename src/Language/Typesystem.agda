module Typesystem where

open import Agda.Builtin.Int renaming (Int to ℤ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary.Decidable using (True; toWitness)

{-

src: https://plfa.github.io/DeBruijn/ 

-}

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
-- infix  5 μ_
infixl 7 _·_
-- infix  8 `suc_
-- infix  9 `_
infix  9 S_
infix  9 #_

data Type : Set where
    -- Base types
    IntTy : Type
    -- Parametric types 
    _⇒_ : Type → Type → Type
    Maybe_ : Type → Type
    List_ : Type → Type
    Either_,_ : Type → Type → Type  

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
    var_ :  ∀ {Γ A}
        → Γ ∋ A
        -----
        → Γ ⊢ A 
    
    -- Add fixpoints or try to integrate them with lambdas
    ƛ_  : ∀ {Γ A B}
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

    -- Maybe
    -- Uncertain about the Nothing constructor 
    Nothing : ∀ {Γ A}
        → Γ ⊢ Maybe A
    Just_ : ∀ {Γ A}
        → Γ ⊢ A
        → Γ ⊢ Maybe A

    -- List
    [] :  ∀ {Γ A}
        → Γ ⊢ List A
    _::_ : ∀ {Γ A}
        → Γ ⊢ A
        → Γ ⊢ List A
        → Γ ⊢ List A
    head : ∀ {Γ A}
        → Γ ⊢ List A
        → Γ ⊢ A
    tail : ∀ {Γ A}
        → Γ ⊢ List A
        → Γ ⊢ List A
        
    -- Either
    Left_ : ∀ {Γ A B}
        → Γ ⊢ A
        → Γ ⊢ Either A , B
    Right_ : ∀ {Γ A B}
        → Γ ⊢ B
        → Γ ⊢ Either A , B

    -- For now only support pattern matching on list/either/maybe
    
    caseM_of_to_or_to_ : ∀ {Γ A B }    
        -- thing ur matching on
        → Γ ⊢ Maybe A
        -- case Nothing
        → Γ ⊢ Maybe A
        → Γ ⊢ B
        -- case Just x
        → Γ ⊢ Maybe A
        → Γ , A ⊢ B
        -- Result
        → Γ ⊢ B
    
    caseL_of_to_or_to_ : ∀ {Γ A B }    
        -- thing ur matching on
        → Γ ⊢ List A
        -- case []
        → Γ ⊢ List A
        → Γ ⊢ B
        -- case x :: xs
        → Γ ⊢ List A
        → Γ , A ⊢ B
        -- Result
        → Γ ⊢ B
    
    caseE_of_to_or_to_ : ∀ {Γ A B C }    
        -- thing ur matching on
        → Γ ⊢ Either A , B
        -- case Left
        → Γ ⊢ Either A , B
        → Γ , A ⊢ C
        -- case Right
        → Γ ⊢ Either A , B
        → Γ , B ⊢ C
        -- Result
        → Γ ⊢ C

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
#_ n {n∈Γ}  =  var count (toWitness n∈Γ)