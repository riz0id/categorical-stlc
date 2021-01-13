{-# OPTIONS --safe --without-K #-}

module Syntax.Var.Categorical where

open import Con

open import Categories.Category
open import Function using (flip)
open import Relation.Binary
open import Subst.Core
open import Syntax.Var
open import Syntax.Var.Properties
open import Level

open import Relation.Binary.PropositionalEquality hiding ([_])

private
  variable
    Γ Δ Θ Ξ : Con
    σ τ : Ty

--------------------------------------------------------------------------------
-- Properties of _∘_

assoc
  :  {u : Subst Var Γ Δ}
  → {v : Subst Var Δ Θ}
  → {w : Subst Var Θ Ξ}
  → u ∘ (v ∘ w) ≡ (u ∘ v) ∘ w
assoc {u = u} {v = v} {w = w} = sym (∘-assoc-svar u v w)

sym-assoc
  :  {u : Subst Var Γ Δ}
  → {v : Subst Var Δ Θ}
  → {w : Subst Var Θ Ξ}
  → (u ∘ v) ∘ w ≡ u ∘ (v ∘ w)
sym-assoc {u = u} {v = v} {w = w} = ∘-assoc-svar u v w

identityˡ : {s : Subst Var Γ Δ} → s ∘ idS ≡ s
identityˡ {s = s} = ∘-neutralˡ-var s

identityʳ : {s : Subst Var Γ Δ} → idS ∘ s ≡ s
identityʳ {s = s} = ∘-neutralʳ-var s

identity² : idS Var ∣ Γ * ∘ idS ≡ idS
identity² {Γ = Γ} = ∘-neutralʳ-var idS Γ *

∘-resp-≈
  :  {x u : Subst Var Δ Θ} → {y v : Subst Var Γ Δ}
  → x ≡ u → y ≡ v → y ∘ x ≡ v ∘ u
∘-resp-≈ refl refl = cong₂ _∘_ refl refl


--------------------------------------------------------------------------------
-- Structures

-- Syntactic category of substitutions over variables.
SynC-Var : Category 0ℓ 0ℓ 0ℓ
SynC-Var = record
  { Obj       = Con
  ; _⇒_      = Subst Var
  ; _≈_       = _≡_
  ; id        = idS
  ; _∘_       = flip _∘_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ  = identityˡ
  ; identityʳ  = identityʳ
  ; identity² = identity²
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = ∘-resp-≈
  }
