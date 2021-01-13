{-# OPTIONS --safe --without-K #-}

module Syntax.Var.Properties where

open import Con.Core
open import Subst.Core
open import Syntax.Var

open import Algebra.Definitions
open import Algebra.Structures
import Data.Product as Π
open import Relation.Binary.PropositionalEquality hiding ([_])

private
  variable
    Γ Δ Θ Ξ : Con
    σ τ : Ty


--------------------------------------------------------------------------------
-- Properties of Variables and Substitution

[]-commutes-⁺ : (s : Subst Var Γ Δ) → (v : Var Δ σ) → v [ s ⁺ τ ] ≡ v [ s ] ⁺ τ
[]-commutes-⁺ (ext s x) vz     = refl
[]-commutes-⁺ (ext s x) (vs v) = []-commutes-⁺ s v


--------------------------------------------------------------------------------
-- Properties of Variables and Weakening

v[idS]≡v⁺τ : (v : Var Γ σ) → v [ idS ] ≡ v
v[idS]≡v⁺τ vz         = refl
v[idS]≡v⁺τ (vs {τ} v) = begin
  v [ idS ⁺ τ ] ≡⟨ []-commutes-⁺ idS v ⟩
  v [ idS ] ⁺ τ ≡⟨ cong weak (v[idS]≡v⁺τ v) ⟩
  vs v          ∎
  where open ≡-Reasoning

v[idS⁺τ]≡v⁺τ : (v : Var Γ σ) → v [ idS ⁺ τ ] ≡ v ⁺ τ
v[idS⁺τ]≡v⁺τ         vz     = []-commutes-⁺ idS vz
v[idS⁺τ]≡v⁺τ {τ = ρ} (vs v) = begin
  vs v [ idS ⁺ ρ ] ≡⟨ []-commutes-⁺ idS (vs v) ⟩
  vs v [ idS ] ⁺ ρ ≡⟨ cong (_⁺ ρ) (v[idS]≡v⁺τ (vs v)) ⟩
  vs v ⁺ ρ         ∎
  where open ≡-Reasoning

v[idS⁺⁺τ]≡v⁺τ : (v : Var (Γ , τ) σ) → v [ idS ⁺⁺ τ ] ≡ v
v[idS⁺⁺τ]≡v⁺τ         vz     = refl
v[idS⁺⁺τ]≡v⁺τ {Γ} {τ} (vs v) = v[idS⁺τ]≡v⁺τ v


--------------------------------------------------------------------------------
-- Properties of Variables and Composition

∘-neutralʳ-var : (s : Subst Var Γ Δ) → idS ∘ s ≡ s
∘-neutralʳ-var ε         = refl
∘-neutralʳ-var (ext s v) = cong₂ ext (∘-neutralʳ-var s) (v[idS]≡v⁺τ v)

∘-neutralˡ-var : (s : Subst Var Γ Δ) → s ∘ idS ≡ s
∘-neutralˡ-var ε         = refl
∘-neutralˡ-var (ext s v) = cong₂ ext (trans (lem s idS v) (∘-neutralˡ-var s)) refl
  where lem : (s : Subst Var Γ Δ) →
              (s' : Subst Var Δ Θ) →
              (v : Var Γ σ) →
              ext s v ∘ s' ⁺ σ ≡ s ∘ s'
        lem _ ε          _ = refl
        lem s (ext s' _) v = cong₂ ext (lem s s' v) refl

-- Note. agda-categories identity is reversed relative to agda-stdlib and
-- agda-categories is prioritized so this definition seems backwards.
∘-identity : Identity _≡_ idS Var ∣ Γ * _∘_
∘-identity = ∘-neutralʳ-var Π., ∘-neutralˡ-var

∘-assoc-var
  :  (u  : Subst Var Γ Δ)
  → (v  : Subst Var Δ Θ)
  → (v' : Var Θ σ)
  → v' [ u ∘ v ] ≡ (v' [ v ]) [ u ]
∘-assoc-var _ (ext _ _) vz      = refl
∘-assoc-var u (ext v _) (vs v') = ∘-assoc-var u v v'

∘-assoc-svar
  :  (u : Subst Var Γ Δ)
  → (v : Subst Var Δ Θ)
  → (w : Subst Var Θ Ξ)
  → (u ∘ v) ∘ w ≡ u ∘ (v ∘ w)
∘-assoc-svar _ _ ε         = refl
∘-assoc-svar u v (ext w t) = cong₂ ext (∘-assoc-svar u v w) (∘-assoc-var u v t)


--------------------------------------------------------------------------------
-- Structures

∘-isMagma : IsMagma _≡_ (_∘_ {Var} {Γ})
∘-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _∘_
  }

∘-isSemigroup : IsSemigroup _≡_ (_∘_ {Var} {Γ})
∘-isSemigroup = record
  { isMagma = ∘-isMagma
  ; assoc   = ∘-assoc-svar
  }

∘-isMonoid : IsMonoid _≡_ _∘_ (idS Γ *)
∘-isMonoid = record
  { isSemigroup = ∘-isSemigroup
  ; identity    = ∘-identity
  }
