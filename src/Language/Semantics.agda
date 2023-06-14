module Semantics where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Integer using (ℤ) renaming (_+_ to _+z_; _-_ to _-z_; _*_ to _*z_)
open import Typesystem

{-

src: https://plfa.github.io/Denotational/ 

-}


data Env : {n : ℕ} → Context n → Set  

-- Index this over types
data Value : Type → Set where
    IntV : ℤ → Value IntTy
    
    -- MaybeTy
    NothingV : ∀ {ty} → Value (MaybeTy ty)
    -- Not sure if this should take a value or a Term
    JustV : ∀ {ty} → Value ty → Value (MaybeTy ty)

    -- ListTy
    NilV : ∀ {ty} → Value (ListTy ty)
    ConsV : ∀ {ty} → Value ty → Value (ListTy ty) → Value (ListTy ty)

    -- EitherTy
    LeftV : ∀ {A B} → Value A → Value (EitherTy A B)
    RightV : ∀ {A B} → Value B → Value (EitherTy A B)

    ClosV : ∀ {n} {Γ : Context n} {argTy retTy} → Env Γ →  Γ , argTy ⊢ retTy → Value (argTy ⇒ retTy)

data Env where
    ∅' : Env ∅
    _,'_ : ∀ {l ty} {Γ : Context l} → Env Γ → (v : Value ty) → Env (Γ , ty)

-- Maybe cite jeoren? 
v-lookup : ∀ {l ty} {Γ : Context l} → Env Γ → Γ ∋ ty → Value ty
v-lookup (γ ,' v) Z = v
v-lookup (γ ,' v) (S l) = v-lookup γ l

infix 3 _⊢e_↓_

data _⊢e_↓_ : ∀ {n} {Γ : Context n} {ty : Type} → Env Γ → (Γ ⊢ ty ) → Value ty → Set where
    ↓var : ∀ {n} {Γ : Context n} {γ : Env Γ} {ty : Type} -- {x : Γ ∋ ty}
        → (x : Γ ∋ ty)
        → γ ⊢e var x ↓ v-lookup γ x
    
    ↓ƛ : ∀ {n} {Γ : Context n} {γ : Env Γ} {argTy retTy : Type} {body : Γ , argTy ⊢ retTy }
        → γ ⊢e ƛ body ↓ ClosV γ body

    -- Maybe I can already enforce / declare context size here?
    ↓· : ∀ {n m} {Γ : Context n} {Γ-clos : Context m} {γ : Env Γ} {γ-clos : Env Γ-clos} {argTy retTy : Type} {arg : Γ ⊢ argTy} {argVal : Value argTy}  {body : Γ-clos , argTy ⊢ retTy } {fun : Γ ⊢ argTy ⇒ retTy} {res}
        -- evaluate function
        → γ ⊢e fun ↓ ClosV γ-clos body
        -- evaluate argument
        → γ ⊢e arg ↓ argVal
        -- evaluate body, extended by argument
        → γ-clos ,' argVal ⊢e body ↓ res
        → γ ⊢e fun · arg ↓ res
    

    -- Int and Int operations
    ↓Int : ∀ {n} {Γ : Context n} {i} {γ : Env Γ}
        → γ ⊢e Int i ↓ IntV i
    ↓+ : ∀ {n} {Γ : Context n} {γ : Env Γ} {i j : ℤ} { l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l + r ↓ IntV (i +z j) 
    ↓- : ∀ {n} {Γ : Context n} {γ : Env Γ} {i j l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l - r ↓ IntV (i -z j) 
    ↓* : ∀ {n} {Γ : Context n} {γ : Env Γ} {i j l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l * r ↓ IntV (i *z j) 
    
    -- Currently all these assume inner Type is always IntTy

    -- MaybeTy
    ↓Nothing : ∀ {n} {Γ : Context n} {A} {γ : Env Γ}
        → γ ⊢e Nothing {A = A} ↓ NothingV
    
    ↓Just : ∀ {n} {Γ : Context n} { val} {γ : Env Γ} {inner : Γ ⊢ IntTy}
        -- thing that is wrapping it
        → γ ⊢e inner ↓ val 
        → γ ⊢e Just inner ↓ JustV val 
    
    -- ListTy
    ↓[] : ∀ {n} {Γ : Context n} { A} {γ : Env Γ}
        → γ ⊢e [] {A = A} ↓ NilV
    ↓:: : ∀ {n} {Γ : Context n} { headV tailV} {γ : Env Γ} {head : Γ ⊢ IntTy} {tail : Γ ⊢ ListTy IntTy}
        -- get first type
        → γ ⊢e head ↓ headV
        -- ensure second arg is tail with right type
        → γ ⊢e tail ↓ tailV
        → γ ⊢e head :: tail ↓ ConsV headV tailV 
    
    {-
    ↓headI : ∀ {n} {Γ : Context n} { headV tailV} {γ : Env Γ } {ListTy : Γ ⊢ ListTy IntTy}
        -- evaluate to a ListTy
        → γ ⊢e ListTy ↓ ConsV headV tailV
        → γ ⊢e head ListTy ↓ headV
    ↓tailI : ∀ {n} {Γ : Context n} { headV tailV} {γ : Env Γ } {list : Γ ⊢ ListTy IntTy}
        -- evaluate to a list
        → γ ⊢e list ↓ ConsV headV tailV
        → γ ⊢e tail list ↓ tailV
    -}
      
    -- EitherTy
    ↓Left : ∀ {n} {Γ : Context n} { A B} {val : Value A} {γ : Env Γ } {x : Γ ⊢ A}
        → γ ⊢e x ↓ val
        → γ ⊢e (Left {B = B} x) ↓ LeftV val
    ↓Right : ∀ {n} {Γ : Context n} { B} {val : Value B} {γ : Env Γ } {x : Γ ⊢ B}
        → γ ⊢e x ↓ val
        → γ ⊢e (Right x) ↓ RightV val
    

    -- For now only support pattern matching on list/EitherTy/MaybeTy

    -- Only checking if term is a Just, not checking if it matches the value (if given)  
    ↓caseMJ : ∀ {n} {Γ : Context n} { A B} {val : Value A} {justClauseRes : Value B} {γ : Env Γ } {matchOn : Γ ⊢ MaybeTy A} {justClause : Γ , A ⊢ B} {notClause : Γ ⊢ B}
        -- Check if term being matched on is a Just
        → γ ⊢e matchOn ↓ JustV val
        -- Get result of evaluating Just clause
        → γ ,' val ⊢e justClause ↓ justClauseRes
        → γ ⊢e caseM matchOn of 
            NothingP to notClause
            or
            JustP to justClause ↓ justClauseRes 
    ↓caseMN : ∀ {n} {Γ : Context n} { A B} {notClauseRes : Value B} {γ : Env Γ } {matchOn : Γ ⊢ MaybeTy A} {justClause : Γ , A ⊢ B} {notClause : Γ ⊢ B}
        -- Check if term being matched on is a Just
        → γ ⊢e matchOn ↓ NothingV
        -- Get result of evaluating Just clause
        → γ ⊢e notClause ↓ notClauseRes
        → γ ⊢e caseM matchOn of 
            NothingP to notClause
            or
            JustP to justClause ↓ notClauseRes
    
    ↓caseL:: : ∀ {n} {Γ : Context n} { A B} {hVal : Value A} {tVal : Value (ListTy A)} {::ClauseRes : Value B} {γ : Env Γ } {matchOn : Γ ⊢ ListTy A} {::Clause : Γ , A , ListTy A ⊢ B} {[]Clause : Γ ⊢ B}
        -- Check if term being matched on is a (x::xs)
        → γ ⊢e matchOn ↓ ConsV hVal tVal
        -- Get result of evaluating :: clause
        → (γ ,' hVal) ,' tVal ⊢e ::Clause ↓ ::ClauseRes
        → γ ⊢e caseL matchOn of 
            []P to []Clause
            or
            ::P to ::Clause ↓ ::ClauseRes
    ↓caseL[] : ∀ {n} {Γ : Context n} { A B} {[]ClauseRes : Value B} {γ : Env Γ } {matchOn : Γ ⊢ ListTy A} {::Clause : Γ , A , ListTy A ⊢ B} {[]Clause : Γ ⊢ B}
        -- Check if term being matched on is a (x::xs)
        → γ ⊢e matchOn ↓ NilV
        -- Get result of evaluating :: clause
        → γ ⊢e []Clause ↓ []ClauseRes
        → γ ⊢e caseL matchOn of 
            []P to []Clause
            or
            ::P to ::Clause ↓ []ClauseRes
    {-
    
    caseL_of_to_or_to_ : ∀ {n} {Γ : Context n} { A B }    
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
    
    caseE_of_to_or_to_ : ∀ {n} {Γ : Context n} { A B C }    
        -- thing ur matching on
        → Γ ⊢ EitherTy A , B
        -- case Left
        → Γ ⊢ EitherTy A , B
        → Γ , A ⊢ C
        -- case Right
        → Γ ⊢ EitherTy A , B
        → Γ , B ⊢ C
        -- Result
        → Γ ⊢ C
    -}    
