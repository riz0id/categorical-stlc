{-# OPTIONS --safe --without-K #-}

module Syntax.Term.Properties where

open import Con.Core
open import Syntax.Term
open import Syntax.Var
open import Syntax.Var.Properties
open import Subst.Core

open import Relation.Binary.PropositionalEquality hiding
  ([_])

private
  variable
    Γ Δ Θ Ξ : Con
    σ τ : Ty


--------------------------------------------------------------------------------
-- Properties of Terms and Substitution


--------------------------------------------------------------------------------
-- Properties of Terms and Weakening

term-commutes-⁺ : (s : Var Γ σ) → term (s ⁺ τ) ≡ (term s) ⁺ τ
term-commutes-⁺ vz     = refl
term-commutes-⁺ (vs s) = cong term (sym (v[idS⁺τ]≡v⁺τ (weak s)))

⌈⌉-commutes-⁺ : (s : Subst Var Γ Δ) → (v : Var Γ σ) → ⌈ s ⁺ σ ⌉ ≡ ⌈ s ⌉ ⁺ σ
⌈⌉-commutes-⁺ ε         v = refl
⌈⌉-commutes-⁺ (ext s t) v = cong₂ ext (⌈⌉-commutes-⁺ s v) (term-commutes-⁺ t)


--------------------------------------------------------------------------------
-- Properties of Terms and Composition


--------------------------------------------------------------------------------
-- Properties of Terms
