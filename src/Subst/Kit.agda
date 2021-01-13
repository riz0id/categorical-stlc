{-# OPTIONS --without-K --safe #-}

module Subst.Kit where

open import Con
open import Subst.Core
open import Term

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Algebra.Definitions

private
  variable
    Γ Δ : Con
    σ τ : Ty

--------------------------------------------------------------------------------
-- Weakening

record WeakKit (T : Con → Set) : Set where
  eta-equality
  infixl 6 _⁺_
  field
    _⁺_ : ∀ {Γ} → T Γ → (τ : Ty) → T (Γ , τ)

open WeakKit {{ ... }} public

record WeakKit+ (T : Con → Ty → Set) : Set where
  eta-equality
  field
    {{weakKit}} : ∀ {σ} → WeakKit (λ Γ → T Γ σ)

  field
    var  : ∀ {Γ σ} → Var Γ σ → T Γ σ
    term : ∀ {Γ σ} → T Γ σ → Tm Γ σ

  -- Variant of _⁺_ that weakens implicitly
  weak : T Γ σ → T (Γ , τ) σ
  weak = _⁺ _

open WeakKit+ {{ ... }} public


--------------------------------------------------------------------------------
-- Substitution

record SubstKit (T : Con → Ty → Set) : Set where
  eta-equality
  field
    {{kit}} : WeakKit+ T
    subst   : ∀ {Γ Δ σ} → T Δ σ → Subst T Γ Δ → T Γ σ

open SubstKit {{ ... }} public
