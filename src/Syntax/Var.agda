{-# OPTIONS --safe --without-K #-}

module Syntax.Var where

open import Con.Core
open import Subst.Core
open import Syntax.Var.Core public
open import Syntax.Term.Core

open import Function using (id)

private
  variable
    Γ Δ Θ Ξ : Con
    σ τ : Ty
    T : Con → Ty → Set


--------------------------------------------------------------------------------
-- Operations

infixl 6 _[_]

weakVar : Var Γ σ → (τ : Ty) → Var (Γ , τ) σ
weakVar v τ = vs {τ} v

-- Substiution
_[_] : Var Δ σ → Subst T Γ Δ → T Γ σ
vz   [ ext s t ] = t
vs v [ ext s t ] = v [ s ]


--------------------------------------------------------------------------------
-- Instances

instance
  -- Variable weakening
  VarWeakKit : WeakKit (λ Γ → Var Γ σ)
  VarWeakKit = record { _⁺_ = weakVar }

  -- Variable syntax
  VarWeakKit+ : SyntaxKit Var
  VarWeakKit+ = record
    { var       = id
    ; term      = vT
    }

  -- Variable substitution
  VarSubstKit : SubstKit Var
  VarSubstKit = record
    { subst = _[_]
    }
