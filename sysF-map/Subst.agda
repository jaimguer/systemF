module Subst where

open import Data.Nat
open import Data.Bool
open import Base
open import Map
open import Shifting

termSubst : ℕ → Term → Term → Term
termSubst j s t = tmMap
                  (λ x → λ y → (if (== x j) then (termShift j s) else (TmVar x)))
                  (λ x → λ y → y)
                  j t

termSubstTop : Term → Term → Term
termSubstTop s t = negTermShift 1 (termSubst 0 (termShift 1 s) t)

typeSubst : Type → ℕ → Type → Type
typeSubst σ j τ = tyMap
                  (λ j → λ x → if (== x j) then (typeShift j σ) else (TyVar x))
                  j τ

typeSubstTop : Type → Type → Type 
typeSubstTop σ τ = negTypeShift 1 (typeSubst (typeShift 1 σ) 0 τ)

tyTermSubst : Type → ℕ → Term → Term
tyTermSubst σ j t = tmMap
                      (λ c → λ x → (TmVar x))
                      (λ j → λ τ → (typeSubst σ j τ))
                      j t

tyTermSubstTop : Type → Term → Term 
tyTermSubstTop σ t = negTermShift 1 (tyTermSubst (typeShift 1 σ) 0 t)
