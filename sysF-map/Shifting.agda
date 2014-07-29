module Shifting where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Base
open import Map

typeShiftAbove : ℕ → ℕ → Type → Type
typeShiftAbove d c τ = tyMap
                       (λ c → λ x → (if (geq x c)
                                     then (TyVar (x + d))
                                     else (TyVar x)))
                       c τ

negTypeShiftAbove : ℕ → ℕ → Type → Type 
negTypeShiftAbove d c τ = tyMap
                          (λ cut → λ x → if (geq x cut)
                                         then (TyVar (x ∸ d))
                                         else TyVar x)
                          c τ  


termShiftType : ℕ → (ℕ → Type → Type)
termShiftType n = typeShiftAbove n


termShiftAbove : ℕ → ℕ → Term → Term
termShiftAbove d c t = tmMap
                       (λ cut → λ x → (if (geq x cut)
                                       then (TmVar (x + d))
                                       else TmVar x))
                       (termShiftType d)
                       c t

                       
negTermShiftAbove : ℕ → ℕ → Term → Term
negTermShiftAbove d c t = tmMap
                       (λ cut → λ x → (if (geq x cut)
                                      then (TmVar (x ∸ d))
                                      else TmVar x))
                       (termShiftType d)
                       c t


termShift : ℕ → Term → Term
termShift d t = termShiftAbove d 0 t

negTermShift : ℕ → Term → Term
negTermShift d t = negTermShiftAbove d 0 t

typeShift : ℕ → Type → Type
typeShift d τ = typeShiftAbove d 0 τ

negTypeShift : ℕ → Type → Type
negTypeShift d τ = negTypeShiftAbove d 0 τ

bindingShift : ℕ → Maybe Binding → Maybe Binding
bindingShift n (just (VarBind τ))     = just (VarBind (typeShift n τ))
bindingShift n (just TyVarBind)       = just TyVarBind
bindingShift n (just (TyAbbBind τ))   = just (TyAbbBind (typeShift n τ))
bindingShift n (just (TmAbbBind t σ)) = just (TmAbbBind (termShift n t) σ)
bindingShift n nothing                = nothing

getBinding : ℕ → Ctx →  Maybe Binding
getBinding i c = bindingShift (suc i) (lookup i c)
