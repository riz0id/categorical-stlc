{-# OPTIONS --safe --without-K #-}

module Syntax.Var.Core where

open import Con.Core

private
  variable
    Γ : Con
    σ τ : Ty

--------------------------------------------------------------------------------
-- Types

-- Variables in De Bruijn representation
data Var : Con → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ , σ) σ
  vs : ∀ {τ Γ σ} → Var Γ σ → Var (Γ , τ) σ
