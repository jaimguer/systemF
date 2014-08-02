module Subst where

open import Data.Nat
open import Data.Bool
open import Base
open import Shifting


{-
  Primary substitution method for terms.
  j : Lower bound index of free variable to be substituted
  s : Term that will replace variable j
-}
termSubst : ℕ → Term → Term → Term
termSubst j s Empty      = Empty
termSubst j s True       = True
termSubst j s False      = False
termSubst j s (Num n)    = (Num n)
termSubst j s (Succ n)   = Succ (termSubst j s n)
termSubst j s (If q f r) = If (termSubst j s q)
                              (termSubst j s f)
                               (termSubst j s r)
termSubst j s (Var x) with (== x j)
... | true  = (termShift j s)
... | false = (Var x)

-- Increment to ensure only free variables are substituted.
termSubst j s (Lam τ body)     = Lam τ (termSubst (suc j) s body)
termSubst j s (App rator rand) = App (termSubst j s rator)
                                     (termSubst j s rand)
termSubst j s (TypeAbs body)      = TypeAbs (termSubst (suc j) s body)
termSubst j s (TypeApp exp τ)     = TypeApp (termSubst j s exp) τ

{-
  Primary substitution method for types.
-}
typeSubst : Type → ℕ → Type → Type
typeSubst σ j Empty     = Empty
typeSubst σ j Boolean   = Boolean
typeSubst σ j Nat       = Nat

typeSubst σ j (TypeVar x) with (== x j)
... | true  = (typeShift j σ)
... | false = (TypeVar x)

typeSubst σ j (α ⇒ β)   = (typeSubst σ j α) ⇒ (typeSubst σ j β)
typeSubst σ j (Forall β) = Forall (typeSubst σ (suc j) β)

{-
  Substitute the free variables
  s : the term to be substituted
  t : the term into which the substitution will occurr
  The inner termSubst substitutes for all free variables within t.
  Because of the inner termShift, the variables will all have indicies
  one larger than they should.
  The negTermShift decrements all variables indices by 1
-}
termSubstTop : Term → Term → Term
termSubstTop s t = negTermShift 1 (termSubst 0 (termShift 1 s) t)
-- (Lam Nat (App (Var 1) (Var 2))) (Lam Nat (App (Var 1) (Var 2)))
-- (Lam Nat (App (Var 2) (Var 3)))
--
{-
  Substitute the free types
  s : the type to be substituted
  t : the type into which the substitution will occur
  This operation is analogous to the above termSubstTop
-}
typeSubstTop : Type → Type → Type
typeSubstTop σ τ = negTypeShift 1 (typeSubst (typeShift 1 σ) 0 τ)

{-
  Substitute a type into a type abstraction
-}
tyTermSubst : Type → ℕ → Term → Term
tyTermSubst σ j Empty    = Empty
tyTermSubst σ j True     = True
tyTermSubst σ j False    = False
tyTermSubst σ j (Succ n) = Succ (tyTermSubst σ j n)
tyTermSubst σ j (Num n)  = (Num n)
tyTermSubst σ j (Var x)  = (Var x)
tyTermSubst σ j (If q f s) = If (tyTermSubst σ j q)
                                (tyTermSubst σ j f)
                                (tyTermSubst σ j s)
tyTermSubst σ j (Lam τ body)     = Lam (typeSubst σ j τ) (tyTermSubst σ (suc j) body)
tyTermSubst σ j (App rator rand) = App (tyTermSubst σ j rator)
                                       (tyTermSubst σ j rand)
tyTermSubst σ j (TypeAbs β)      = TypeAbs (tyTermSubst σ (suc j) β)
tyTermSubst σ j (TypeApp exp τ)  = TypeApp (tyTermSubst σ j exp) (typeSubst σ j τ)


{-
  Substitute a type into the
  the "outermost" free type variable.
-}
tyTermSubstTop : Type → Term → Term
tyTermSubstTop σ t = negTermShift 1 (tyTermSubst (typeShift 1 σ) 0 t)
