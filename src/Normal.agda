{-# OPTIONS --safe --without-K #-}

module Normal where

open import Con
open import Term

mutual
  data Sp : Con → Ty → Ty → Set where
    ε⃗ : ∀ {Γ σ} → Sp Γ σ σ
    _,_ : ∀ {Γ σ τ ρ} → Nf Γ σ → Sp Γ τ ρ → Sp Γ (σ ⟶ τ) ρ

  data Nf : Con → Ty → Set where
    εN : ∀ {Γ σ} → Var Γ σ → Sp Γ σ ⊤ → Nf Γ ⊤
    λN : ∀ {Γ σ τ} → Nf (Γ , σ) τ → Nf Γ (σ ⟶ τ)
