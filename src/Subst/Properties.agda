{-# OPTIONS --safe --without-K #-}

module Subst.Properties where


--------------------------------------------------------------------------------
-- Properties of Terms

-- term-commutes-⁺ : (s : Var Γ σ) → term (s ⁺ τ) ≡ (term s) ⁺ τ
-- term-commutes-⁺ vz     = refl
-- term-commutes-⁺ (vs s) = cong vT (sym (v[idS⁺τ]≡v⁺τ (vs s)))

-- ⌈⌉-commute : (s : Subst Var Γ Δ) → (v : Var Γ σ) → ⌈ s ⁺ σ ⌉ ≡ ⌈ s ⌉ ⁺ σ
-- ⌈⌉-commute ε         v = refl
-- ⌈⌉-commute (ext s t) v = cong₂ ext (⌈⌉-commute s v) (term-commutes-⁺ t)
