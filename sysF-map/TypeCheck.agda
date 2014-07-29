module TypeCheck where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Maybe
open import Base
open import Map
open import Shifting
open import Subst


getTyAbb : ℕ → Ctx →  Type
getTyAbb n c with (getBinding n c)
... | just (TyAbbBind τ) = τ
... | _                  = Empty


typeEq : Type → Type → Ctx →  Bool
typeEq Empty    Empty      c = true
typeEq Boolean  Boolean    c = true
typeEq Nat      Nat        c = true
typeEq (y ⇒ y') (z ⇒ z')   c = (And (typeEq y z c) (typeEq y' z' c))
typeEq (TyVar i) σ         c = typeEq (getTyAbb i c) σ c
typeEq τ         (TyVar j) c = typeEq τ (getTyAbb j c) c
typeEq (TyAll y) (TyAll z) c = (typeEq y z c)
typeEq _         _         _           = false 


getTypeFromContext : ℕ → Ctx → Maybe Type
getTypeFromContext i c with (getBinding i c)
... | just (VarBind τ)     = just τ
... | just (TmAbbBind _ τ) = just τ
... | just TyVarBind       = nothing
... | just (TyAbbBind x)   = nothing
... | _                    = nothing

type-of : Term → Ctx →  Type
type-of Empty    c = Empty
type-of TmTrue   c = Boolean
type-of TmFalse  c = Boolean
type-of (Num n)  c = Nat
type-of (Succ n) c with (type-of n c)
... | Nat = Nat
... | _   = Empty

type-of (TmIf q a b) c = if (typeEq (type-of q c) Boolean c)
                         then (if (typeEq (type-of a c) (type-of b c) c)
                               then (type-of a c)
                               else Empty)
                         else Empty
                         --then (let τ = (type-of a c)
                         --      in (if (typeEq τ (type-of b c) c)
                         --          then τ
                         --          else Empty))
                         --else Empty

type-of (TmVar i) c = (maybeYank (getTypeFromContext i c))
type-of (TmAbs τ body) c = let σ = type-of body ((VarBind τ) ∷ c)
                            in τ ⇒ (negTypeShift 1 σ)
type-of (TmApp rator rand) c = let τ = type-of rator c
                               in let σ = type-of rand c
                                  in (if (isArrow τ)
                                      then (conseq τ)
                                      else Empty)

type-of (TmTAbs body) c = TyAll (type-of body (TyVarBind ∷ c))
type-of (TmTApp e τ) c with (type-of e c)
... | TyAll σ = typeSubstTop τ σ
... | _ = Empty


--#################################--
id : Term
id = TmTAbs (TmAbs (TyVar 0) (TmVar 0))

double : Term
double = (TmTAbs (TmAbs ((TyVar 0) ⇒ (TyVar 0)) (TmAbs (TyVar 0) (TmApp (TmVar 1) (TmApp (TmVar 1) (TmVar 0))))))

quad : Term
quad = TmTAbs (TmApp (TmTApp double ((TyVar 0) ⇒ (TyVar 0))) (TmTApp double (TyVar 0)))

t : Type
t = type-of (TmTApp double ((TyVar 0) ⇒ (TyVar 0))) [] 

s : Type 
s = type-of (TmTApp double (TyVar 0)) []

typeTest1 : Type
typeTest1 = type-of (TmAbs Nat (TmVar 0)) []

typeTest2 : Type
typeTest2 = type-of (TmApp (TmAbs (Nat ⇒ Nat) (TmVar 0)) (TmAbs Nat (TmVar 0))) []

typeTest3 : Type
typeTest3 = type-of (TmApp (TmTApp (TmTAbs (TmAbs (TyVar 0) (TmVar 0))) (Nat ⇒ Nat)) (TmTApp (TmTAbs (TmVar 0)) Nat)) []

typeTest4 : Type
typeTest4 = type-of (TmAbs (Nat ⇒ Nat) (TmAbs Nat (TmApp (TmVar 1) (TmApp (TmVar 1) (TmVar 0))))) []

typeTest5 : Type
typeTest5 = type-of (TmApp (TmAbs (Boolean ⇒ Boolean) (TmIf (TmApp (TmVar 0) TmFalse) TmTrue TmFalse))
                           (TmAbs Boolean (TmIf (TmVar 0) TmFalse TmTrue))) []

typeTest6 : Type
typeTest6 = type-of (TmTApp (TmTAbs (TmAbs (TyVar 0) (TmVar 0))) (TyAll (TyVar 0))) []

typeTest7 : Type
typeTest7 = type-of id []

typeTest8 : Type
typeTest8 = type-of double []

typeTest9 : Type
typeTest9 = type-of quad []
