module Map where

open import Data.Nat
open import Base

{-
  Mapping function for types.
  f : a function applied to term variables
  c : cutoff number
-}
tyMap : (ℕ → ℕ → Type) → ℕ → Type → Type
tyMap f c (TyVar i) = (f c i)
tyMap f c Empty     = Empty
tyMap f c Boolean   = Boolean
tyMap f c Nat       = Nat
tyMap f c (y ⇒ y')  = (tyMap f c y) ⇒ (tyMap f c y')
tyMap f c (TyAll y) = TyAll (tyMap f (suc c) y)


{-
  Mapping function for terms.
  f : a function applied to term variables
  g : a function applied to types
-}
tmMap : (ℕ → ℕ → Term) → (ℕ → Type → Type) → ℕ → Term → Term
tmMap f g c Empty         = Empty
tmMap f g c (Num y)       = Num y
tmMap f g c TmTrue        = TmTrue
tmMap f g c TmFalse       = TmFalse
tmMap f g c (Succ n)      = Succ (tmMap f g c n)
tmMap f g c (TmIf q a b)  = TmIf (tmMap f g c q)
                                 (tmMap f g c a)
                                 (tmMap f g c b)
tmMap f g c (TmVar y)     = (f c y)
tmMap f g c (TmAbs y y')  = TmAbs (g c y) (tmMap f g (suc c) y')
tmMap f g c (TmApp y y')  = TmApp (tmMap f g c y) (tmMap f g c y')
tmMap f g c (TmTAbs y)    = TmTAbs (tmMap f g (suc c) y)
tmMap f g c (TmTApp y y') = TmTApp (tmMap f g c y) (g c y')
