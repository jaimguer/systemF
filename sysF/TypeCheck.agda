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
typeEq Empty       Empty       c = true
typeEq Boolean     Boolean     c = true
typeEq Nat         Nat         c = true
typeEq (α ⇒ β)     (τ ⇒ σ)     c = (And (typeEq α τ c)
                                       (typeEq β σ c))
typeEq (TypeVar i) σ           c = typeEq (getTyAbb i c) σ c
typeEq τ           (TypeVar j) c = typeEq τ (getTyAbb j c) c
typeEq (Forall i)  (Forall j)  c = typeEq i j c
typeEq _           _           _  = false

{-
  Function to determine if a function type will receive
  an argument of the appropriate type.
-}
isTypeAligned : Type → Type → Ctx → Bool
isTypeAligned (α ⇒ β) σ c = typeEq σ α c
isTypeAligned _       _ _ = false

{-
  Function to extract type from a context.
  Only returns type for those bindings that
  can hold type information
-}
getTypeFromContext : ℕ → Ctx → Maybe Type
getTypeFromContext i c with (getBinding i c)
... | just (VarBind τ)     = just τ
... | just (TmAbbBind _ τ) = just τ
... | just TypeVarBind     = nothing
... | just (TyAbbBind x)   = nothing
... | _                    = nothing

{-
  Type checker
-}
type-of : Term → Ctx → Type
type-of Empty    c = Empty
type-of True     c = Boolean
type-of False    c = Boolean
type-of (Num n)  c = Nat
type-of (Succ n) c with (type-of n c)
... | Nat = Nat
... | _ = Empty
-- Both branches of the if statement are requred to
-- have the same type
type-of (If q a b) c = if (typeEq (type-of q c) Boolean c)
                         then (let τ = (type-of a c)
                               in (if (typeEq τ (type-of b c) c)
                                   then τ
                                   else Empty))
                         else Empty

type-of (Var i) c = (maybeYank (getTypeFromContext i c))
type-of (Lam τ body) c = let σ = type-of body ((VarBind τ) ∷ c)
                            in τ ⇒ (negTypeShift 1 σ)
type-of (App rator rand) c = let τ = type-of rator c
                               in let σ = type-of rand c
                                  in (if (isArrow τ)
                                      then (if (isTypeAligned τ σ c)
                                            then (conseq τ)
                                            else Empty)
                                      else Empty)
type-of (TypeAbs body) c = Forall (type-of body (TypeVarBind ∷ c))
type-of (TypeApp e τ) c with (type-of e c)
... | Forall σ = typeSubstTop τ σ
... | _ = Empty

--#################################--

id : Term
id = TypeAbs (Lam (TypeVar 0) (Var 0))

double : Term
double = (TypeAbs (Lam ((TypeVar 0) ⇒ (TypeVar 0)) (Lam (TypeVar 0) (App (Var 1) (App (Var 1) (Var 0))))))
 
quad : Term
quad = (TypeAbs (App (TypeApp double ((TypeVar 0) ⇒ (TypeVar 0))) (TypeApp double (TypeVar 0))))

{-
   Input  : (λ x:Nat. x)
   Output : Nat ⇒ Nat
-}
typeTest1 : Type
typeTest1 = type-of (Lam Nat (Var 0)) []

{-
  Input  : ((λ x:(Nat ⇒ Nat) x) (λ x:Nat x))
  Output : Nat ⇒ Nat
-}
typeTest2 : Type
typeTest2 = type-of (App (Lam (Nat ⇒ Nat) (Var 0)) (Lam Nat (Var 0))) []

{-
  Input  : (((Λ X. λ x:X. x) [Nat ⇒ Nat]) ((Λ X. λ x:X. x) [Nat]))
  Output : Nat ⇒ Nat
-}
typeTest3 : Type
typeTest3 = type-of (App (TypeApp (TypeAbs (Lam (TypeVar 0) (Var 0))) (Nat ⇒ Nat)) (TypeApp (TypeAbs (Lam (TypeVar 0) (Var 0))) Nat)) []

{-
  Input  : (λ x:(Nat ⇒ Nat). λ y:Nat. x (x y))
  Output : (Nat ⇒ Nat) ⇒ (Nat ⇒ Nat)
-}
typeTest4 : Type
typeTest4 = type-of (Lam (Nat ⇒ Nat) (Lam Nat (App (Var 1) (App (Var 1) (Var 0))))) []

{-
  Input  : ((λ x:(Bool ⇒ Bool). (If (x False) True False)) (λ x:Bool. (If x False True)))
  Output : Bool
-}
typeTest5 : Type
typeTest5 = type-of (App (Lam (Boolean ⇒ Boolean)
                              (If (App (Var 0) False) True False))
                         (Lam Boolean (If (Var 0) False True))) []

{-
  Input  : ((Λ X. λ x:X x) [∀ x])
  Output : (∀ X) ⇒ (∀ X)
-}
typeTest6 : Type
typeTest6 = type-of (TypeApp (TypeAbs (Lam (TypeVar 0) (Var 0))) (Forall (TypeVar 0))) []

{-
  Input  : (Λ X. λ x:X. x)
  Output : ∀ X.(X ⇒ X)
-}
typeTest7 : Type
typeTest7 = type-of id []

{-
  Input  : (Λ X. λ x:(X ⇒ X). λ y:X. x (x y))
  Output : ∀ X. ((X ⇒ X) ⇒ (X ⇒ X))
-}
typeTest8 : Type
typeTest8 = type-of double []

{-
  Input  : Λ X. ((double [X ⇒ X]) (double [X]))
  Output : ∀ X. ((X ⇒ X) ⇒ (X ⇒ X))
-}
typeTest9 : Type
typeTest9 = type-of quad []
