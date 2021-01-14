{-# OPTIONS --safe --without-K #-}

module Con.Ty where

data Ty : Set where
  ⊤   : Ty
  _⟶_ : Ty → Ty → Ty
  _×_ : Ty → Ty → Ty
