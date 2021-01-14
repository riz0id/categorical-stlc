{-# OPTIONS --safe --without-K #-}

module Syntax.Term.Core where

open import Con.Core
open import Syntax.Var.Core


--------------------------------------------------------------------------------
-- Types

data Term : Con → Ty → Set where
  vT    : ∀ {Γ σ} → Var Γ σ → Term Γ σ
  λT    : ∀ {Γ σ τ} → Term (Γ , σ) τ → Term Γ (σ ⟶ τ)
  ∘T    : ∀ {Γ σ τ} → Term Γ (σ ⟶ τ) → Term Γ σ → Term Γ τ
  ×T    : ∀ {Γ σ τ} → Term Γ σ → Term Γ τ → Term Γ (σ × τ)
  proj₁ : ∀ {Γ σ τ} → Term Γ (σ × τ) → Term Γ σ
  proj₂ : ∀ {Γ σ τ} → Term Γ (σ × τ) → Term Γ τ
