module Base where

open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Maybe

{-
  Basic type definitions
  Type variables, along with universally quanitified
  types are handled by de Bruijn indices rather than
  named binders
-}
data Type : Set where
  Empty   : Type
  Boolean : Type
  Nat     : Type
  TypeVar : ℕ    → Type
  _⇒_     : Type → Type → Type
  Forall  : Type → Type

{-
  Basic term definitions
  Lambda abstractions are now annotated with the
  type of their imput.
  Though this implementation assumes perfect inputs,
  the Empty type and term constructors are necessary
  allow for easy handling of Agda's totality requirement
-}
data Term : Set where
  Empty   : Term
  Num     : ℕ    → Term
  Succ    : Term → Term
  Var     : ℕ    → Term
  Lam     : Type → Term → Term
  App     : Term → Term → Term
  TypeAbs : Term → Term
  TypeApp : Term → Type → Term
  True    : Term
  False   : Term
  If      : Term → Term → Term → Term



{-
  Bindings that will be pushed into the environment/
  typing context during evaluation and type-checking.
  Binding contructors take with them as much information
  as possible about the values they are binding.
-}
data Binding : Set where
  TypeVarBind : Binding
  VarBind     : Type → Binding
  TyAbbBind   : Type → Binding
  TmAbbBind   : Term → Type → Binding

{-
  A context is a list of bindings.  This serves
  a dual purpose as an environment during evaluation,
  and as a context during type checking
-}
Ctx : Set
Ctx = List Binding

{-
  Some helper functions.
-}
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
isVal True         = true
isVal False        = false
isVal (Lam τ body) = true
isVal (TypeAbs body)  = true
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
