module Shifting where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Base

{-
  Method for shifting types.
  Shifting is the process by which type variable indices
  are adjusted "up" during evaluation.
  d : Number of spots to shift the "free" type variables
  c : Cutoff for when to stop shifting
-}
typeShiftAbove : ℕ → ℕ → Type → Type
typeShiftAbove d c Empty   = Empty
typeShiftAbove d c Nat     = Nat
typeShiftAbove d c Boolean = Boolean
typeShiftAbove d c (TypeVar x) with (geq x c)
... | true  = (TypeVar (x + d))
... | false = (TypeVar x)
typeShiftAbove d c (α ⇒ β)   = (typeShiftAbove d c α) ⇒ (typeShiftAbove d c β)
typeShiftAbove d c (Forall β) = Forall (typeShiftAbove d (suc c) β)

{-
  Method for shifting types variable indices "down".
  Rather than using a normal type shifting method that
  can handle integers, this method uses natural numbers
  and merely subtracts them when the index is greater than
  or equal to the cutoff.
-}
negTypeShiftAbove : ℕ → ℕ → Type → Type
negTypeShiftAbove d c Empty     = Empty
negTypeShiftAbove d c Nat       = Nat
negTypeShiftAbove d c Boolean   = Boolean
negTypeShiftAbove d c (TypeVar x) with (geq x c)
... | true  = (TypeVar (x ∸ d))
... | false = (TypeVar x)
negTypeShiftAbove d c (α ⇒ β)   = (negTypeShiftAbove d c α) ⇒ (negTypeShiftAbove d c β)
negTypeShiftAbove d c (Forall β) = Forall (negTypeShiftAbove d (suc c) β)

{-
  Method for shifting term variables "up".
  Analogous to typeShiftAbove in functionality.
  d : Number of spots to shift the free variables
  c : Cutoff for when to stop shifting
-}
termShiftAbove : ℕ → ℕ → Term → Term
termShiftAbove d c Empty    = Empty
termShiftAbove d c (Num n)  = (Num n)
termShiftAbove d c (Succ n) = Succ (termShiftAbove d c n)
termShiftAbove d c True     = True
termShiftAbove d c False    = False
termShiftAbove d c (Var x) with (geq x c)
... | true  = (Var (x + d))
... | false = (Var x)
termShiftAbove d c (If q f s) = If (termShiftAbove d c q)
                                   (termShiftAbove d c f)
                                   (termShiftAbove d c s)
termShiftAbove d c (Lam τ body)     = Lam (typeShiftAbove d c τ)
                                          (termShiftAbove d (suc c) body)
termShiftAbove d c (App rator rand) = App (termShiftAbove d c rator)
                                          (termShiftAbove d c rand)
termShiftAbove d c (TypeAbs t)         = TypeAbs (termShiftAbove d (suc c) t)
termShiftAbove d c (TypeApp e τ)       = TypeApp (termShiftAbove d c e)
                                                 (typeShiftAbove d c τ)
{-
  Method for shifting term variables "down".
  Analogous to negTypeShiftAbove in functionality.
-}
negTermShiftAbove : ℕ → ℕ → Term → Term
negTermShiftAbove d c Empty    = Empty
negTermShiftAbove d c (Num n)  = (Num n)
negTermShiftAbove d c (Succ n) = Succ (negTermShiftAbove d c n)
negTermShiftAbove d c True     = True
negTermShiftAbove d c False    = False
negTermShiftAbove d c (Var x) with (geq x c)
... | true  = (Var (x ∸ d))
... | false = (Var x)
negTermShiftAbove d c (If q f s) = If (negTermShiftAbove d c q)
                                      (negTermShiftAbove d c f)
                                      (negTermShiftAbove d c s)
negTermShiftAbove d c (Lam τ body) = Lam (typeShiftAbove d c τ)
                                         (negTermShiftAbove d (suc c) body)
negTermShiftAbove d c (App rator rand) = App (negTermShiftAbove d c rator)
                                             (negTermShiftAbove d c rand)
negTermShiftAbove d c (TypeAbs t)         = TypeAbs (negTermShiftAbove d (suc c) t)
negTermShiftAbove d c (TypeApp e τ)       = TypeApp (negTermShiftAbove d c e)
                                                    (negTypeShiftAbove d c τ)

{-
  Helper functions. Will shift all term variables
-}
termShift : ℕ → Term → Term
termShift d t = termShiftAbove d 0 t

negTermShift : ℕ → Term → Term
negTermShift d t = negTermShiftAbove d 0 t

{-
  Helper functions. Will shift all type variables
-}
typeShift : ℕ → Type → Type
typeShift d t = typeShiftAbove d 0 t

negTypeShift : ℕ → Type → Type
negTypeShift d t = negTypeShiftAbove d 0 t

{-
  Method to shift the information held within bindings by
  a certain number of places.
  d : Number of places to shift.
-}
bindingShift : ℕ → Maybe Binding → Maybe Binding
bindingShift d (just (VarBind τ))     = just (VarBind (typeShift d τ))
bindingShift d (just TypeVarBind)     = just TypeVarBind
bindingShift d (just (TyAbbBind τ))   = just (TyAbbBind (typeShift d τ))
bindingShift d (just (TmAbbBind t σ)) = just (TmAbbBind (termShift d t) σ)
bindingShift d nothing                = nothing

{-
  Method to extract a binding from a context while performing
  any necessary shifts.
-}
getBinding : ℕ → Ctx → Maybe Binding
getBinding i c = bindingShift (suc i) (lookup i c)

