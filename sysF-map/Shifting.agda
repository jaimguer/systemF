module Shifting where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Base
open import Map

{-
  Function to shift types "upward".
-}
typeShiftAbove : ℕ → ℕ → Type → Type
typeShiftAbove d c τ = tyMap
                       (λ c → λ x → (if (geq x c)
                                     then (TypeVar (x + d))
                                     else (TypeVar x)))
                       c τ
{-
  Function to shift types "downward"
-}
negTypeShiftAbove : ℕ → ℕ → Type → Type 
negTypeShiftAbove d c τ = tyMap
                          (λ cut → λ x → if (geq x cut)
                                         then (TypeVar (x ∸ d))
                                         else TypeVar x)
                          c τ  

{-
  Helper for termShiftAbove that generates a function
  to be applied to types
-}
termShiftType : ℕ → (ℕ → Type → Type)
termShiftType n = typeShiftAbove n

{-
  Function to shift term variables up.
-}
termShiftAbove : ℕ → ℕ → Term → Term
termShiftAbove d c t = tmMap
                       (λ cut → λ x → (if (geq x cut)
                                       then (Var (x + d))
                                       else Var x))
                       (termShiftType d)
                       c t

{-
  Function to shift term variables down
-}
negTermShiftAbove : ℕ → ℕ → Term → Term
negTermShiftAbove d c t = tmMap
                          (λ cut → λ x → (if (geq x cut)
                                         then (Var (x ∸ d))
                                         else Var x))
                          (termShiftType d)
                          c t

{-
  Helpers to shift all term variables
-}
termShift : ℕ → Term → Term
termShift d t = termShiftAbove d 0 t

negTermShift : ℕ → Term → Term
negTermShift d t = negTermShiftAbove d 0 t

{-
  Helpers to shift all type variables
-}
typeShift : ℕ → Type → Type
typeShift d τ = typeShiftAbove d 0 τ

negTypeShift : ℕ → Type → Type
negTypeShift d τ = negTypeShiftAbove d 0 τ

{-
  Function to shift information within bindings
-}
bindingShift : ℕ → Maybe Binding → Maybe Binding
bindingShift n (just (VarBind τ))     = just (VarBind (typeShift n τ))
bindingShift n (just TypeVarBind)       = just TypeVarBind
bindingShift n (just (TyAbbBind τ))   = just (TyAbbBind (typeShift n τ))
bindingShift n (just (TmAbbBind t σ)) = just (TmAbbBind (termShift n t) σ)
bindingShift n nothing                = nothing

{-
  Extract a binding from a context
-}
getBinding : ℕ → Ctx →  Maybe Binding
getBinding i c = bindingShift (suc i) (lookup i c)
