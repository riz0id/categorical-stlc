{-# OPTIONS --safe --without-K #-}

module Syntax.Term.Categorical.Category where

open import Con
open import Syntax

open import Function using (flip)
open import Level
open import Relation.Binary.PropositionalEquality hiding (erefl; [_])

open import Categories.Category


--------------------------------------------------------------------------------
-- Structures



Tm : Ty → Ty → Set
Tm σ τ = Term (ε , σ) τ



λId : ∀ {σ} → Tm σ σ
λId = vT vz

--------------------------------------------------------------------------------
-- Structures

TermCategory : Category 0ℓ 0ℓ 0ℓ
TermCategory = record
  { Obj       = Ty
  ; _⇒_      = Tm
  ; _≈_       = _≡_
  ; id        = λId
  ; _∘_       = {!flip ∘T!}
  ; assoc     = {!!}
  ; sym-assoc = {!!}
  ; identityˡ  = {!!}
  ; identityʳ  = {!!}
  ; identity² = {!!}
  ; equiv     = {!!}
  ; ∘-resp-≈  = {!!}
  }
