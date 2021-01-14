{-# OPTIONS --safe --without-K #-}

module Syntax.Var.Categorical.Exponential where

open import Con
open import Subst.Core
open import Syntax.Var
open import Syntax.Var.Categorical.Category

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories.Object.Exponential VarCategory


--------------------------------------------------------------------------------
-- Structures

VarExponential : {Γ Δ : Con} → Exponential Γ Δ
VarExponential {Γ} {Δ} = record
  { B^A      = {!!}
  ; product  = {!!}
  ; eval     = {!!}
  ; λg       = {!!}
  ; β        = {!!}
  ; λ-unique = {!!}
  }
