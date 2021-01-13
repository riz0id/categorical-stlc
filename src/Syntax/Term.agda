{-# OPTIONS --safe --without-K #-}

module Syntax.Term where

open import Con.Core
open import Subst.Core
open import Syntax.Var

open import Function using (id)

private
  variable
    Γ Δ Θ Ξ : Con
    σ τ : Ty
    T : Con → Ty → Set


--------------------------------------------------------------------------------
-- Re-exports

open import Syntax.Term.Core public


--------------------------------------------------------------------------------
-- Operations

substTerm : {{SyntaxKit T}} → Term Δ σ → Subst T Γ Δ → Term Γ σ
substTerm (vT v)     s = term (v [ s ])
substTerm (λT t)     s = λT (substTerm t (s ⁺⁺ _))
substTerm (∘T t₁ t₂) s = ∘T (substTerm t₁ s) (substTerm t₂ s)

weakTerm : Term Γ σ → (τ : Ty) → Term (Γ , τ) σ
weakTerm tm τ = substTerm tm (idS ⁺ τ)


--------------------------------------------------------------------------------
-- Instances

instance
  TermWeakKit : WeakKit (λ Γ → Term Γ σ)
  TermWeakKit = record { _⁺_ = weakTerm }

  TermSyntaxKit : SyntaxKit Term
  TermSyntaxKit = record
    { var       = vT
    ; term      = id
    }

  TermSubstKit : SubstKit Term
  TermSubstKit = record { subst = substTerm }
