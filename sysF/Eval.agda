module Eval where

open import Data.List
open import Data.Maybe
open import Data.Bool
open import Base
open import Shifting
open import Subst


{-
  Primary evaluation procedure.
  The bodies of lambda abstractions
  are not evaluated
-}
value-of : Term → Ctx → Term
value-of (Num n)  c = (Num n)
value-of TmTrue   c = TmTrue
value-of TmFalse  c = TmFalse
value-of (Succ n) c = Succ (value-of n c)

value-of (TmIf TmTrue a b) c  = value-of a c
value-of (TmIf TmFalse a b) c = value-of b c
value-of (TmIf q a b) c       = value-of (TmIf (value-of q c) a b) c

value-of (TmVar n) c with (getBinding n c)
... | just (TmAbbBind term type) = term
... | _                          = Empty

value-of (TmAbs τ body) c = (TmAbs τ body)

value-of (TmApp (TmAbs τ body) v) c with (isVal v)
... | true  = (termSubstTop v body)
... | false =  value-of (TmApp (TmAbs τ body) (value-of v c)) c

value-of (TmTApp (TmTAbs body) τ) c = value-of (tyTermSubstTop τ body) c
value-of (TmApp rator rand)       c = value-of (TmApp (value-of rator c) rand) c
value-of (TmTApp exp τ)           c = (TmTApp (value-of exp c) τ)
value-of _                        _ = Empty

{-
  Some test programs
-}

valTest1 : Term
valTest1 = value-of (TmApp (TmAbs Nat (TmVar 0)) (Num 1)) []

valTest2 : Term
valTest2 = value-of (TmApp (TmAbs Nat (TmVar 0)) (TmApp (TmAbs Nat (TmVar 0)) (Num 2))) []

valTest3 : Term
valTest3 = value-of (TmApp (TmTApp (TmTAbs (TmAbs (TyVar 0) (TmVar 0))) Nat) (Num 3)) []

valTest4 : Term
valTest4 = value-of (TmApp (TmAbs Nat (Succ (TmVar 0))) (Num 4)) []

valTest5 : Term
valTest5 = value-of (TmApp (TmAbs Nat (Succ (TmVar 0))) (TmApp (TmAbs Nat (TmVar 0)) (Num 5))) []

valTest6 : Term
valTest6 = value-of (TmApp (TmTApp (TmTAbs (TmAbs (TyVar 0) (TmVar 0))) Nat) (Num 6)) []

valTest7 : Term
valTest7 = value-of (TmTApp (TmTAbs (TmAbs (TyVar 0) (TmVar 0))) Nat) []
