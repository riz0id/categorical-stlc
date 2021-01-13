{-# OPTIONS --safe --without-K #-}

module Subst.Core where

open import Con
open import Syntax.Term.Core
open import Syntax.Var.Core

private
  variable
    Γ Δ Θ Ξ : Con
    σ τ : Ty
    T : Con → Ty → Set

--------------------------------------------------------------------------------
-- Types

data Subst (T : Con → Ty → Set) : Con → Con → Set where
  ε   : ∀ {Γ} → Subst T Γ ε
  ext : ∀ {Γ Δ σ} → Subst T Γ Δ → T Γ σ → Subst T Γ (Δ , σ)


--------------------------------------------------------------------------------
-- Structures

-- Weak rule
record WeakKit (T : Con → Set) : Set where
  eta-equality
  infixl 6 _⁺_
  field
    _⁺_ : ∀ {Γ} → T Γ → (τ : Ty) → T (Γ , τ)

open WeakKit {{ ... }} public

-- Syntactic embeddings
record SyntaxKit (T : Con → Ty → Set) : Set where
  eta-equality
  field
    {{weakKit}} : ∀ {σ} → WeakKit (λ Γ → T Γ σ)

  field
    var  : ∀ {Γ σ} → Var Γ σ → T Γ σ
    term : ∀ {Γ σ} → T Γ σ → Term Γ σ

  -- Variant of _⁺_ that weakens implicitly
  weak : T Γ σ → T (Γ , τ) σ
  weak = _⁺ _

open SyntaxKit {{ ... }} public

-- Substitution rule
record SubstKit (T : Con → Ty → Set) : Set where
  eta-equality
  field
    {{kit}} : SyntaxKit T

  field
    subst : ∀ {Γ Δ σ} → T Δ σ → Subst T Γ Δ → T Γ σ

open SubstKit {{ ... }} public


--------------------------------------------------------------------------------
-- Operations

infixl 6 _⁺⁺_
infixl 5 _∘_

-- Weakening
weakSubst : {{SyntaxKit T}} → Subst T Γ Δ → (τ : Ty) → Subst T (Γ , τ) Δ
weakSubst ε         τ = ε
weakSubst (ext s x) τ = ext (weakSubst s τ) (x ⁺ τ)

-- Lifting
_⁺⁺_ : {{SyntaxKit T}} → Subst T Γ Δ → (σ : Ty) → Subst T (Γ , σ) (Δ , σ)
u ⁺⁺ σ = ext (weakSubst u σ) (var vz)

-- Composition
_∘_ : {{SubstKit T}} → Subst T Γ Δ → Subst T Δ Θ → Subst T Γ Θ
u ∘ ε       = ε
u ∘ ext v t = ext (u ∘ v) (subst t u)

-- Embedding
⌈_⌉ : {{SyntaxKit T}} → Subst T Γ Δ → Subst Term Γ Δ
⌈ ε       ⌉ = ε
⌈ ext s v ⌉ = ext ⌈ s ⌉ (term v)


--------------------------------------------------------------------------------
-- Constants

-- Identity substitution
idS : {{SyntaxKit T}} → Subst T Γ Γ
idS {Γ = ε}     = ε
idS {Γ = Γ , x} = idS ⁺⁺ x

-- Variant of the identity substitution with an explicit context.
idS_* : {{SyntaxKit T}} → (Γ : Con) → Subst T Γ Γ
idS_* Γ = idS {_} {Γ}

-- Variant of the identity substitution with an explicit context and prototype.
idS_∣_* : (T : Con → Ty → Set) → {{SyntaxKit T}} → (Γ : Con) → Subst T Γ Γ
idS_∣_* T Γ = idS {T} {Γ}



--------------------------------------------------------------------------------
-- Instances

instance
  SubstWeakKit : {{SyntaxKit T}} → WeakKit (λ Γ → Subst T Γ Δ)
  SubstWeakKit = record { _⁺_ = weakSubst }
