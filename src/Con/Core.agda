{-# OPTIONS --safe --without-K #-}

module Con.Core where

open import Con.Ty public

infixl 5 _,_
data Con : Set where
  ε   : Con
  -- ^ empty context
  _,_ : Con → Ty → Con
  -- ^ context extension
