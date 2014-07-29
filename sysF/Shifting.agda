module Shifting where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Base

{-
  Method for shifting types.
  Shifting is the process by which type variable indices
  are adjusted "up" during evaluation.
  Given a ... and a cutoff...
-}
typeShiftAbove : ℕ → ℕ → Type → Type
typeShiftAbove d c Empty   = Empty
typeShiftAbove d c Nat     = Nat
typeShiftAbove d c Boolean = Boolean
typeShiftAbove d c (TyVar x) with (geq x c)
... | true  = (TyVar (x + d))
... | false = (TyVar x)
typeShiftAbove d c (α ⇒ β)   = (typeShiftAbove d c α) ⇒ (typeShiftAbove d c β)
typeShiftAbove d c (TyAll β) = TyAll (typeShiftAbove d (suc c) β)

{-
  Method for shifting types variable indices "down".
  Rather than using a normal type shifting method that
  can handle integers, this method sticks with natural numbers
  and merely subtracts them when the index is greater than
  or equal to the cutoff
-}
negTypeShiftAbove : ℕ → ℕ → Type → Type
negTypeShiftAbove d c Empty     = Empty
negTypeShiftAbove d c Nat       = Nat
negTypeShiftAbove d c Boolean   = Boolean
negTypeShiftAbove d c (TyVar x) with (geq x c)
... | true  = (TyVar (x ∸ d))
... | false = (TyVar x)
negTypeShiftAbove d c (α ⇒ β)   = (negTypeShiftAbove d c α) ⇒ (negTypeShiftAbove d c β)
negTypeShiftAbove d c (TyAll β) = TyAll (negTypeShiftAbove d (suc c) β)

{-
  Method for shifting term variables "up".
  Analogous to typeShiftAbove in functionality.
-}
termShiftAbove : ℕ → ℕ → Term → Term
termShiftAbove d c (Succ n) = Succ (termShiftAbove d c n)
termShiftAbove d c Empty = Empty
termShiftAbove d c (Num n)            = (Num n)
termShiftAbove d c TmTrue = TmTrue
termShiftAbove d c TmFalse = TmFalse
termShiftAbove d c (TmVar x) with (geq x c)
... | true  = (TmVar (x + d))
... | false = (TmVar x)
termShiftAbove d c (TmIf q f s) = TmIf (termShiftAbove d c q)
                                         (termShiftAbove d c f)
                                         (termShiftAbove d c s)
termShiftAbove d c (TmAbs τ body)     = TmAbs (typeShiftAbove d c τ)
                                              (termShiftAbove d (suc c) body)
termShiftAbove d c (TmApp rator rand) = TmApp (termShiftAbove d c rator)
                                              (termShiftAbove d c rand)
termShiftAbove d c (TmTAbs t)         = TmTAbs (termShiftAbove d (suc c) t)
termShiftAbove d c (TmTApp e τ)       = TmTApp (termShiftAbove d c e)
                                               (typeShiftAbove d c τ)
{-
  Method for shifting term variables "down".
  Analogous to negTypeShiftAbove in functionality.
-}
negTermShiftAbove : ℕ → ℕ → Term → Term
negTermShiftAbove d c Empty              = Empty
negTermShiftAbove d c (Succ n) = Succ (negTermShiftAbove d c n)
negTermShiftAbove d c (Num n)            = (Num n)
negTermShiftAbove d c TmTrue = TmTrue
negTermShiftAbove d c TmFalse = TmFalse
negTermShiftAbove d c (TmVar x) with (geq x c)
... | true  = (TmVar (x ∸ d))
... | false = (TmVar x)
negTermShiftAbove d c (TmIf q f s) = TmIf (negTermShiftAbove d c q)
                                          (negTermShiftAbove d c f)
                                          (negTermShiftAbove d c s)
negTermShiftAbove d c (TmAbs τ body)     = TmAbs (typeShiftAbove d c τ)
                                                 (negTermShiftAbove d (suc c) body)
negTermShiftAbove d c (TmApp rator rand) = TmApp (negTermShiftAbove d c rator)
                                                 (negTermShiftAbove d c rand)
negTermShiftAbove d c (TmTAbs t)         = TmTAbs (negTermShiftAbove d (suc c) t)
negTermShiftAbove d c (TmTApp e τ)       = TmTApp (negTermShiftAbove d c e)
                                                  (negTypeShiftAbove d c τ)

{-
  Helper function. Will always consume the terms with index 0
-}
termShift : ℕ → Term → Term
termShift d t = termShiftAbove d 0 t

negTermShift : ℕ → Term → Term
negTermShift d t = negTermShiftAbove d 0 t

{-
  Helper function. Will always consume the types with index 0
-}
typeShift : ℕ → Type → Type
typeShift d t = typeShiftAbove d 0 t

negTypeShift : ℕ → Type → Type
negTypeShift d t = negTypeShiftAbove d 0 t

bindingShift : ℕ → Maybe Binding → Maybe Binding
bindingShift d (just (VarBind τ))     = just (VarBind (typeShift d τ))
bindingShift d (just TyVarBind)       = just TyVarBind
bindingShift d (just (TyAbbBind τ))   = just (TyAbbBind (typeShift d τ))
bindingShift d (just (TmAbbBind t σ)) = just (TmAbbBind (termShift d t) σ)
bindingShift d nothing                = nothing

getBinding : ℕ → Ctx → Maybe Binding
getBinding i c = bindingShift (suc i) (lookup i c)

