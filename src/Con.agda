{-# OPTIONS --safe --without-K #-}

module Con where

open import Con.Core public
open import Con.Ty public


-- infixl 6 _-_
-- _-_ : ∀ {σ} → (Γ : Con) → Var Γ σ → Con
-- (Γ , _) - vz   = Γ
-- (Γ , σ) - vs v = Γ - v , σ
