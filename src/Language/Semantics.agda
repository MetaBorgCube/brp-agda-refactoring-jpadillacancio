module Semantics where

open import Data.Integer using (ℤ) renaming (_+_ to _+z_; _-_ to _-z_; _*_ to _*z_)
open import Typesystem

{-

src: https://plfa.github.io/Denotational/ 

-}


Env : Context → Set 

data Value : Set where
    IntV : ℤ → Value
    
    -- Maybe
    NothingV : Value
    -- Not sure if this should take a value or a Term
    JustV : Value → Value

    -- List
    NilV : Value
    ConsV : Value → Value → Value

    -- Either
    LeftV : Value → Value
    RightV : Value → Value

    ClosV : ∀ {Γ} {argTy retTy} → Env Γ → Γ , argTy ⊢ retTy → Value


Env Γ =  {t : Type} → ∀ (x : Γ ∋ t ) → Value

infix 3 _⊢e_↓_

data _⊢e_↓_ : ∀ {Γ : Context} {ty : Type} → Env Γ → (Γ ⊢ ty ) → Value → Set where
    ↓var : ∀ {Γ} {γ : Env Γ} {ty : Type} -- {x : Γ ∋ ty}
        → (x : Γ ∋ ty)
        → γ ⊢e var x ↓ γ x
    
    ↓ƛ : ∀ {Γ} {γ : Env Γ} {argTy retTy : Type} {body : Γ , argTy ⊢ retTy }
        → γ ⊢e ƛ  body ↓ ClosV γ body

    ↓· : ∀ {Γ Γ-clos} {γ : Env Γ} {γ-clos : Env Γ-clos} {argTy retTy : Type} {arg : Γ ⊢ argTy} {γ-app : Env (Γ-clos , argTy)}  {body : Γ-clos , argTy ⊢ retTy } {fun : Γ ⊢ argTy ⇒ retTy} {res}
        -- evaluate to function
        → γ ⊢e fun ↓ ClosV γ-clos body
        -- evalue body under extended closure environment
        -- Is this wrong? Should I be constructing the environment? Maybe create a context list-like data structure?
        → γ-app ⊢e body ↓ res
        → γ ⊢e fun · arg ↓ res

    -- Int and Int operations
    ↓Int : ∀ {Γ} {i} {γ : Env Γ}
        → γ ⊢e Int i ↓ IntV i
    ↓+ : ∀ {Γ} {γ : Env Γ} {i j : ℤ} { l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l + r ↓ IntV (i +z j) 
    ↓- : ∀ {Γ} {γ : Env Γ} {i j l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l - r ↓ IntV (i -z j) 
    ↓* : ∀ {Γ} {γ : Env Γ} {i j l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l * r ↓ IntV (i *z j) 
    
    -- Currently all these assume inner Type is always IntTy

    -- Maybe
    ↓Nothing : ∀ {Γ A} {γ : Env Γ}
        → γ ⊢e Nothing {_} {A} ↓ NothingV
    
    ↓Just : ∀ {Γ val} {γ : Env Γ} {inner : Γ ⊢ IntTy}
        -- thing that is wrapping it
        → γ ⊢e inner ↓ val 
        → γ ⊢e Just inner ↓ JustV val 
    
    -- List
    ↓[] : ∀ {Γ A} {γ : Env Γ}
        → γ ⊢e [] {_}  {A} ↓ NilV
    ↓_::_ : ∀ {Γ headV tailV} {γ : Env Γ} {head : Γ ⊢ IntTy} {tail : Γ ⊢ List IntTy}
        -- get first type
        → γ ⊢e head ↓ headV
        -- ensure second arg is tail with right type
        → γ ⊢e tail ↓ tailV
        → γ ⊢e head :: tail ↓ ConsV headV tailV 
    
    
    ↓headI : ∀ {Γ headV tailV} {γ : Env Γ } {list : Γ ⊢ List IntTy}
        -- evaluate to a list
        → γ ⊢e list ↓ ConsV headV tailV
        → γ ⊢e head list ↓ headV
    ↓tailI : ∀ {Γ headV tailV} {γ : Env Γ } {list : Γ ⊢ List IntTy}
        -- evaluate to a list
        → γ ⊢e list ↓ ConsV headV tailV
        → γ ⊢e tail list ↓ tailV
        
    -- Either
    ↓Left : ∀ {Γ val A B } {γ : Env Γ } {x : Γ ⊢ A}
        → γ ⊢e x ↓ val
        → γ ⊢e (Left {_} {_} {B} x) ↓ LeftV val
    ↓Right : ∀ {Γ val A B} {γ : Env Γ } {x : Γ ⊢ B}
        → γ ⊢e x ↓ val
        → γ ⊢e (Right {_} {_} {A} x) ↓ RightV val
    
    -- For now only support pattern matching on list/either/maybe

    -- Only checking if term is a Just, not checking if it matches the value (if given)  
    ↓caseMJ : ∀ {Γ val justClauseRes A} {γ : Env Γ } {γ-j : Env (Γ , A) } {matchOn : Γ ⊢ Maybe A} {justClause : Γ , A ⊢ A} {notClause : Γ ⊢ A}
        -- Check if term being matched on is a Just
        → γ ⊢e matchOn ↓ JustV val
        -- Get result of evaluating Just clause
        → γ-j ⊢e justClause ↓ justClauseRes
        → γ ⊢e caseM matchOn of 
            NothingP to notClause
            or
            JustP to justClause ↓ justClauseRes 
    ↓caseMN : ∀ {Γ notClauseRes A} {γ : Env Γ } {γ-j : Env (Γ , A) } {matchOn : Γ ⊢ Maybe A} {justClause : Γ , A ⊢ A} {notClause : Γ ⊢ A}
        -- Check if term being matched on is a Just
        → γ ⊢e matchOn ↓ NothingV
        -- Get result of evaluating Just clause
        → γ ⊢e notClause ↓ notClauseRes
        → γ ⊢e caseM matchOn of 
            NothingP to notClause
            or
            JustP to justClause ↓ notClauseRes 
    
    {-
    
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
    -}    