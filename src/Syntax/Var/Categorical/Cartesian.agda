{-# OPTIONS --safe --without-K #-}

module Syntax.Var.Categorical.Cartesian where

open import Con
open import Subst.Core
open import Syntax.Var
open import Syntax.Var.Properties
open import Syntax.Var.Categorical.Category
open import Syntax.Var.Categorical.Product
open import Syntax.Var.Categorical.Terminal

import Data.Product as Σ
open import Relation.Binary.PropositionalEquality hiding (erefl; [_])

open import Categories.Category.Cartesian VarCategory

private
  variable
    Γ Δ Θ Ξ : Con
    σ τ : Ty


------------------------------------------------------------------------------
-- Constants

π₁ : ∀ {Γ Δ σ} {s : Subst Var Γ (Δ , σ)} → Subst Var Γ Δ
π₁ {s = ext s _} = s

π₂ : {s : Subst Var Γ (Δ , σ)} → Var Γ σ
π₂ {s = s} = vz [ s ]


------------------------------------------------------------------------------
-- Properties

VarBinaryProduct : BinaryProducts
VarBinaryProduct = record
  { product = {!!}
  }

VarCartesian : Cartesian
VarCartesian = record
  { terminal = VarTerminal
  ; products = VarBinaryProduct
  }


-- ⟨_,_⟩ ?:  ∀ {Ξ} → Subst Var Ξ Γ → Subst Var Ξ Δ → Subst Var Ξ Γ×Δ
-- ∀ {Γ} → {u : Subst Var Γ ?1} {v : Subst Var Γ ?2} → ?6 u v ∘ ?4 ≡ u
