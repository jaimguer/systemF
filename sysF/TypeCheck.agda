module TypeCheck where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Maybe
open import Base
open import Shifting
open import Subst

{-
  Pulls type abstractions out of a context.
  Specifically, this returns the type associated
  with the type abstraction's binding.
-}
getTyAbb : ℕ → Ctx → Type
getTyAbb n c with (getBinding n c)
... | just (TyAbbBind τ) = τ
... | _ = Empty

{-
  Function to determine if two types are equal.
-}
typeEq : Type → Type → Ctx →  Bool
typeEq Empty     Empty       c = true
typeEq Boolean   Boolean     c = true
typeEq Nat       Nat         c = true
typeEq (α ⇒ β)   (τ ⇒ σ)     c = (And (typeEq α τ c)
                                       (typeEq β σ c))
typeEq (TypeVar i) σ         c = typeEq (getTyAbb i c) σ c
typeEq τ         (TypeVar j) c = typeEq τ (getTyAbb j c) c
typeEq (Forall i) (Forall j) c = typeEq i j c
typeEq _ _ _                 = false

{-
  Function to determine if a function type will receive
  an argument of the appropriate type.
-}
isTypeAligned : Type → Type → Ctx → Bool
isTypeAligned (α ⇒ β) σ c = typeEq σ α c
isTypeAligned _ _ _ = false

{-
  Function to extract type from a context.
  Only returns type for those bindings that
  can hold type information
-}
getTypeFromContext : ℕ → Ctx → Maybe Type
getTypeFromContext i c with (getBinding i c)
... | just (VarBind τ)     = just τ
... | just (TmAbbBind _ τ) = just τ
... | just TypeVarBind       = nothing
... | just (TyAbbBind x)   = nothing
... | _                    = nothing

{-
  Type checker
-}
type-of : Term → Ctx → Type
type-of Empty   c = Empty
type-of TmTrue  c = Boolean
type-of TmFalse c = Boolean
type-of (Num n) c = Nat
type-of (Succ n) c with (type-of n c)
... | Nat = Nat
... | _ = Empty
-- Both branches of the if statement are requred to
-- have the same type
type-of (TmIf q a b) c = if (typeEq (type-of q c) Boolean c)
                         then (let τ = (type-of a c)
                               in (if (typeEq τ (type-of b c) c)
                                   then τ
                                   else Empty))
                         else Empty

type-of (TmVar i) c = (maybeYank (getTypeFromContext i c))
type-of (TmAbs τ body) c = let σ = type-of body ((VarBind τ) ∷ c)
                            in τ ⇒ (negTypeShift 1 σ)
type-of (TmApp rator rand) c = let τ = type-of rator c
                               in let σ = type-of rand c
                                  in (if (isArrow τ)
                                      then (if (isTypeAligned τ σ c)
                                            then (conseq τ)
                                            else Empty)
                                      else Empty)
type-of (TmTAbs body) c = Forall (type-of body (TypeVarBind ∷ c))
type-of (TmTApp e τ) c with (type-of e c)
... | Forall σ = typeSubstTop τ σ
... | _ = Empty

--#################################--

id : Term
id = TmTAbs (TmAbs (TypeVar 0) (TmVar 0))

double : Term
double = (TmTAbs (TmAbs ((TypeVar 0) ⇒ (TypeVar 0)) (TmAbs (TypeVar 0) (TmApp (TmVar 1) (TmApp (TmVar 1) (TmVar 0))))))
 
quad : Term
quad = (TmTAbs (TmApp (TmTApp double ((TypeVar 0) ⇒ (TypeVar 0))) (TmTApp double (TypeVar 0))))

typeTest1 : Type
typeTest1 = type-of (TmAbs Nat (TmVar 0)) []

typeTest2 : Type
typeTest2 = type-of (TmApp (TmAbs (Nat ⇒ Nat) (TmVar 0)) (TmAbs Nat (TmVar 0))) []

typeTest3 : Type
typeTest3 = type-of (TmApp (TmTApp (TmTAbs (TmAbs (TypeVar 0) (TmVar 0))) (Nat ⇒ Nat)) (TmTApp (TmTAbs (TmAbs (TypeVar 0) (TmVar 0))) Nat)) []


typeTest4 : Type
typeTest4 = type-of (TmAbs (Nat ⇒ Nat) (TmAbs Nat (TmApp (TmVar 1) (TmApp (TmVar 1) (TmVar 0))))) []

typeTest5 : Type
typeTest5 = type-of (TmApp (TmAbs (Boolean ⇒ Boolean) (TmIf (TmApp (TmVar 0) TmFalse) TmTrue TmFalse))
                           (TmAbs Boolean (TmIf (TmVar 0) TmFalse TmTrue))) []

typeTest6 : Type
typeTest6 = type-of (TmTApp (TmTAbs (TmAbs (TypeVar 0) (TmVar 0))) (Forall (TypeVar 0))) []

typeTest7 : Type
typeTest7 = type-of id []

typeTest8 : Type
typeTest8 = type-of double []

typeTest9 : Type
typeTest9 = type-of quad []
