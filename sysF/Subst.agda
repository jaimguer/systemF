module Subst where

open import Data.Nat
open import Data.Bool
open import Base
open import Shifting


{-
  Primary substitution method for terms.
-}

termSubst : ℕ → Term → Term → Term
termSubst j s Empty    = Empty
termSubst j s TmTrue   = TmTrue
termSubst j s TmFalse  = TmFalse
termSubst j s (Num n)  = (Num n)
termSubst j s (Succ n) = Succ (termSubst j s n)
termSubst j s (TmIf q f r) = TmIf (termSubst j s q)
                                  (termSubst j s f)
                                  (termSubst j s r)

termSubst j s (TmVar x) with (== x j)
... | true  = (termShift j s)
... | false = (TmVar x)

termSubst j s (TmAbs τ body)     = TmAbs τ (termSubst (suc j) s body)
termSubst j s (TmApp rator rand) = TmApp (termSubst j s rator)
                                          (termSubst j s rand)
termSubst j s (TmTAbs body)      = TmTAbs (termSubst (suc j) s body)
termSubst j s (TmTApp exp τ)     = TmTApp (termSubst j s exp) τ

{-
  Primary substitution method for types.
-}
typeSubst : Type → ℕ → Type → Type
typeSubst σ j Empty     = Empty
typeSubst σ j Boolean   = Boolean
typeSubst σ j Nat       = Nat

typeSubst σ j (TyVar x) with (== x j)
... | true  = (typeShift j σ)
... | false = (TyVar x)

typeSubst σ j (α ⇒ β)   = (typeSubst σ j α) ⇒ (typeSubst σ j β)
typeSubst σ j (TyAll β) = TyAll (typeSubst σ (suc j) β)

{-
  Substitute the terms with index 0.
  s : the term to be substituted
  t : the term into which the substitution will occurr
-}
termSubstTop : Term → Term → Term
termSubstTop s t = negTermShift 1 (termSubst 0 (termShift 1 s) t)

{-
  Substitute the type with index 0.
  s : the type to be substituted
  t : the type into which the substitution will occurr
-}
typeSubstTop : Type → Type → Type
typeSubstTop σ τ = negTypeShift 1 (typeSubst (typeShift 1 σ) 0 τ)

{-
  Substitute a type into a type abstraction
-}
tyTermSubst : Type → ℕ → Term → Term
tyTermSubst σ j Empty     = Empty
tyTermSubst σ j TmTrue    = TmTrue
tyTermSubst σ j TmFalse   = TmFalse
tyTermSubst σ j (Succ n)  = Succ (tyTermSubst σ j n)
tyTermSubst σ j (Num n)   = (Num n)
tyTermSubst σ j (TmVar x) = (TmVar x)
tyTermSubst σ j (TmIf q f s) = TmIf (tyTermSubst σ j q)
                                    (tyTermSubst σ j f)
                                    (tyTermSubst σ j s)
tyTermSubst σ j (TmAbs τ body)     = TmAbs (typeSubst σ j τ) (tyTermSubst σ (suc j) body)
tyTermSubst σ j (TmApp rator rand) = TmApp (tyTermSubst σ j rator)
                                           (tyTermSubst σ j rand)
tyTermSubst σ j (TmTAbs β)       = TmTAbs (tyTermSubst σ (suc j) β)
tyTermSubst σ j (TmTApp exp τ)     = TmTApp (tyTermSubst σ j exp) (typeSubst σ j τ)


{-
  Substitute a type into the
  "outermost" type variable
-}
tyTermSubstTop : Type → Term → Term
tyTermSubstTop σ t = negTermShift 1 (tyTermSubst (typeShift 1 σ) 0 t)
