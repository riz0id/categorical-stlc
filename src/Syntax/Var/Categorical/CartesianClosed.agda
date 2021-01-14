{-# OPTIONS --safe --without-K #-}

module Syntax.Var.Categorical.CartesianClosed where

open import Con
open import Subst.Core
open import Syntax.Var
open import Syntax.Var.Categorical.Category

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories.Category.CartesianClosed VarCategory


--------------------------------------------------------------------------------
-- Structures

VarCCC : CartesianClosed
VarCCC = record
  { cartesian = {!!}
  ; exp       = {!VarExponential!}
  }
