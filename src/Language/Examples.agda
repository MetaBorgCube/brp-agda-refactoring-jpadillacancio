module Examples where

open import Typesystem
open import Agda.Builtin.Int using (pos)


add1 : ∀ {Γ} → Γ ⊢ IntTy ⇒ IntTy
add1 = ƛ (Int pos 1) + (# 0) 

