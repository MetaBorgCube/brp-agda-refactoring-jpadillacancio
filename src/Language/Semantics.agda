module Semantics where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Integer using (ℤ) renaming (_+_ to _+z_; _-_ to _-z_; _*_ to _*z_)
open import Typesystem

{-

src: https://plfa.github.io/Denotational/ 

-}

private 
    variable
        Γ : Context

        ty : Type

data Env : Context → Set  

data Value : Type → Set where
    IntV : ℤ → Value IntTy
    
    -- MaybeTy
    NothingV : Value (MaybeTy ty)
    JustV : Value ty → Value (MaybeTy ty)

    -- ListTy
    NilV : Value (ListTy ty)
    ConsV : Value ty → Value (ListTy ty) → Value (ListTy ty)

    ClosV : ∀ {argTy retTy} → Env Γ →  Γ , argTy ⊢ retTy → Value (argTy ⇒ retTy)

data Env where
    ∅' : Env ∅
    _,'_ : ∀ {ty}  → Env Γ → (v : Value ty) → Env (Γ , ty)

private
    variable
        γ : Env Γ

v-lookup : ∀ {ty}  → Env Γ → Γ ∋ ty → Value ty
v-lookup (γ ,' v) Z = v
v-lookup (γ ,' v) (S l) = v-lookup γ l

infix 3 _⊢e_↓_

data _⊢e_↓_ : Env Γ → (Γ ⊢ ty ) → Value ty → Set where
    ↓var :  
        (x : Γ ∋ ty)
        → γ ⊢e var x ↓ v-lookup γ x
    
    ↓ƛ : ∀ {argTy retTy : Type} {body : Γ , argTy ⊢ retTy }
        → γ ⊢e ƛ body ↓ ClosV γ body

    ↓· : ∀ {Γ-clos : Context} {γ-clos : Env Γ-clos} {argTy retTy : Type} {arg : Γ ⊢ argTy} {argVal : Value argTy}  {body : Γ-clos , argTy ⊢ retTy } {fun : Γ ⊢ argTy ⇒ retTy} {res}
        -- evaluate function
        → γ ⊢e fun ↓ ClosV γ-clos body
        -- evaluate argument
        → γ ⊢e arg ↓ argVal
        -- evaluate body, extended by argument
        → γ-clos ,' argVal ⊢e body ↓ res
        → γ ⊢e fun · arg ↓ res
    

    -- Int and Int operations
    ↓Int : ∀  {i} 
        → γ ⊢e Int i ↓ IntV i
    ↓+ : ∀   {i j : ℤ} { l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l + r ↓ IntV (i +z j) 
    ↓- : ∀   {i j l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l - r ↓ IntV (i -z j) 
    ↓* : ∀   {i j l r} 
        -- Eval lhs
        → γ ⊢e l ↓ IntV i
        -- Eval rhs
        → γ ⊢e r ↓ IntV j
        → γ ⊢e l * r ↓ IntV (i *z j) 

    -- MaybeTy
    ↓Nothing : ∀  {A} 
        → γ ⊢e Nothing {A = A} ↓ NothingV
    
    ↓Just : ∀ {val}  {inner : Γ ⊢ IntTy}
        -- thing that it is wrapping
        → γ ⊢e inner ↓ val 
        → γ ⊢e Just inner ↓ JustV val 
    
    -- ListTy
    ↓[] : ∀ {A} 
        → γ ⊢e [] {A = A} ↓ NilV
    ↓:: : ∀ {headV tailV} {head : Γ ⊢ IntTy} {tail : Γ ⊢ ListTy IntTy}
        -- get first type
        → γ ⊢e head ↓ headV
        -- ensure second arg is tail with right type
        → γ ⊢e tail ↓ tailV
        → γ ⊢e head :: tail ↓ ConsV headV tailV 
    
    -- For now only support pattern matching on ListTy/MaybeTy
    -- Pattern matching is hardcoded, first is a nothing/empty list, second is just/nonempty list

    ↓caseMJ : ∀ {A B} {val : Value A} {justClauseRes : Value B} {matchOn : Γ ⊢ MaybeTy A} {justClause : Γ , A ⊢ B} {notClause : Γ ⊢ B}
        -- Check if term being matched on is a Just
        → γ ⊢e matchOn ↓ JustV val
        -- Get result of evaluating Just clause
        → γ ,' val ⊢e justClause ↓ justClauseRes
        → γ ⊢e caseM matchOn of 
            NothingP to notClause
            or
            JustP to justClause ↓ justClauseRes 
    ↓caseMN : ∀  { A B} {notClauseRes : Value B} {matchOn : Γ ⊢ MaybeTy A} {justClause : Γ , A ⊢ B} {notClause : Γ ⊢ B}
        -- Check if term being matched on is a Nothing
        → γ ⊢e matchOn ↓ NothingV
        -- Get result of evaluating Nothing clause
        → γ ⊢e notClause ↓ notClauseRes
        → γ ⊢e caseM matchOn of 
            NothingP to notClause
            or
            JustP to justClause ↓ notClauseRes
    
    ↓caseL:: : ∀  { A B} {hVal : Value A} {tVal : Value (ListTy A)} {::ClauseRes : Value B} {matchOn : Γ ⊢ ListTy A} {::Clause : Γ , A , ListTy A ⊢ B} {[]Clause : Γ ⊢ B}
        -- Check if term being matched on is a (x::xs)
        → γ ⊢e matchOn ↓ ConsV hVal tVal
        -- Get result of evaluating :: clause
        → (γ ,' hVal) ,' tVal ⊢e ::Clause ↓ ::ClauseRes
        → γ ⊢e caseL matchOn of 
            []P to []Clause
            or
            ::P to ::Clause ↓ ::ClauseRes
    ↓caseL[] : ∀  { A B} {[]ClauseRes : Value B} {matchOn : Γ ⊢ ListTy A} {::Clause : Γ , A , ListTy A ⊢ B} {[]Clause : Γ ⊢ B}
        -- Check if term being matched on is a []
        → γ ⊢e matchOn ↓ NilV
        -- Get result of evaluating [] clause
        → γ ⊢e []Clause ↓ []ClauseRes
        → γ ⊢e caseL matchOn of 
            []P to []Clause
            or
            ::P to ::Clause ↓ []ClauseRes