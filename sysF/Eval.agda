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
value-of True     c = True
value-of False    c = False
value-of (Succ n) c = Succ (value-of n c)

value-of (If True a b)  c = value-of a c
value-of (If False a b) c = value-of b c
value-of (If q a b)     c = value-of (If (value-of q c) a b) c

value-of (Var n) c with (getBinding n c)
... | just (TmAbbBind term type) = term
... | _                          = Empty

value-of (Lam τ body) c = (Lam τ body)

value-of (App (Lam τ body) v) c with (isVal v)
... | true  = (termSubstTop v body)
... | false =  value-of (App (Lam τ body) (value-of v c)) c

value-of (App rator rand)           c = value-of (App (value-of rator c) rand) c
value-of (TypeApp (TypeAbs body) τ) c = value-of (tyTermSubstTop τ body) c
value-of (TypeApp exp τ)            c = (TypeApp (value-of exp c) τ)
value-of _                          _ = Empty

{-
  Some test programs
-}
valTest1 : Term
valTest1 = value-of (App (Lam Nat (Var 0)) (Num 1)) []

valTest2 : Term
valTest2 = value-of (App (Lam Nat (Var 0)) (App (Lam Nat (Var 0)) (Num 2))) []

valTest3 : Term
valTest3 = value-of (App (TypeApp (TypeAbs (Lam (TypeVar 0) (Var 0))) Nat) (Num 3)) []

valTest4 : Term
valTest4 = value-of (App (Lam Nat (Succ (Var 0))) (Num 4)) []

valTest5 : Term
valTest5 = value-of (App (Lam Nat (Succ (Var 0))) (App (Lam Nat (Var 0)) (Num 5))) []

valTest6 : Term
valTest6 = value-of (If True (App (TypeApp (TypeAbs (Lam (TypeVar 0) (Var 0))) Nat) (Num 6))
                             (If False (Num 7) (Num 8))) []

valTest7 : Term
valTest7 = value-of (TypeApp (TypeAbs (Lam (TypeVar 0) (Var 0))) Nat) []
