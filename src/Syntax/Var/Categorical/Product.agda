{-# OPTIONS --safe --without-K #-}

module Syntax.Var.Categorical.Product where

open import Con
open import Subst.Core
open import Syntax.Var
open import Syntax.Var.Categorical.Category

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Categories.Category
open import Categories.Object.Product VarCategory


------------------------------------------------------------------------------
-- Constants

-- π₁ : ∀ {Γ} → Subst Var Γ Γ
-- π₁ {Γ} = idS

-- π₂ : ∀ {Γ Δ} → Subst Var Γ Δ
-- π₂ {Γ} {ε}     = ε
-- π₂ {Γ} {Δ , σ} = ext (π₂ {Γ} {Δ}) {!!}


--------------------------------------------------------------------------------
-- Structures

VarProduct : ∀ {Γ Δ} → Product Γ Δ
VarProduct {Γ} {Δ} = record
  { A×B      = Γ
  ; π₁       = {!!}
  ; π₂       = {!!}
  ; ⟨_,_⟩    = {!!}
  ; project₁ = {!!}
  ; project₂ = {!!}
  ; unique   = {!!}
  }
