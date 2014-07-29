module Base where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Maybe

data Type : Set where
  Empty   : Type
  Boolean : Type
  Nat     : Type
  TyVar   : ℕ    → Type
  _⇒_     : Type → Type → Type
  TyAll   : Type → Type

data Term : Set where
  Empty   : Term
  Num     : ℕ    → Term
  Succ    : Term → Term
  TmVar   : ℕ    → Term
  TmAbs   : Type → Term → Term
  TmApp   : Term → Term → Term
  TmTAbs  : Term → Term
  TmTApp  : Term → Type → Term
  TmTrue  : Term
  TmFalse : Term
  TmIf    : Term → Term → Term → Term

data Binding : Set where
  TyVarBind : Binding
  VarBind   : Type → Binding
  TyAbbBind : Type → Binding
  TmAbbBind : Term → Type → Binding

Ctx : Set
Ctx = List Binding

ctxLength : Ctx → ℕ
ctxLength [] = 0
ctxLength (x ∷ xs) = (suc (ctxLength xs))



geq : ℕ → ℕ → Bool
geq zero    zero    = true
geq (suc n) zero    = true
geq zero    (suc n) = false
geq (suc n) (suc m) = (geq n m)

lessThan : ℕ → ℕ → Bool
lessThan zero    zero    = false
lessThan zero    (suc n) = true
lessThan (suc n) zero    = false
lessThan (suc n) (suc m) = lessThan n m

== : ℕ → ℕ → Bool
== zero    zero    = true
== (suc n) (suc m) = (== n m)
== _       _       = false

And : Bool → Bool → Bool
And true true = true
And _    _    = false


lookup : ℕ → Ctx → Maybe Binding
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n xs
lookup _ []             = nothing


isVal : Term → Bool
isVal Empty          = true
isVal (Num n)        = true
isVal (Succ n)       = true
isVal TmTrue         = true
isVal TmFalse        = false
isVal (TmAbs τ body) = true
isVal (TmTAbs body)  = true
isVal _              = false

maybeYank : Maybe Type → Type
maybeYank (just τ) = τ
maybeYank nothing = Empty

isArrow : Type → Bool
isArrow (α ⇒ β) = true
isArrow _ = false

conseq : Type → Type
conseq (α ⇒ β) = β
conseq _ = Empty
