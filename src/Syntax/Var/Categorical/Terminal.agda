{-# OPTIONS --safe --without-K #-}

module Syntax.Var.Categorical.Terminal where

open import Con
open import Subst.Core
open import Syntax.Var
open import Syntax.Var.Categorical.Category

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories.Object.Terminal VarCategory

--------------------------------------------------------------------------------
-- Properties

!-unique : ∀ {Γ} → (f : Subst Var Γ ε) → ε ≡ f
!-unique ε = refl


--------------------------------------------------------------------------------
-- Structures

ε-isTerminal : IsTerminal ε
ε-isTerminal = record
  { !        = ε
  ; !-unique = !-unique
  }

VarTerminal : Terminal
VarTerminal = record
  { ⊤             = ε
  ; ⊤-is-terminal = ε-isTerminal
  }
