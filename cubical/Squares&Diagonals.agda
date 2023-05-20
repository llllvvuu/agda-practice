{-# OPTIONS --cubical #-}
module Squares&Diagonals where
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

variable ℓ : Level
variable A : Type ℓ

reflRefl : {a : A} → refl {x = a} ≡ refl {x = a}
reflRefl {a = a} i j = a

module UseOfSquares
  (a b c d : A)
  (p : a ≡ b)
  (q : a ≡ b)
  (s : p ≡ q)
  where

  left : a ≡ b
  left = s i0

  right : a ≡ b
  right = s i1

  top : a ≡ a
  top i = s i i0

  bottom : b ≡ b
  bottom i = s i i1

  rotate : (sym q) ≡ (sym p)
  rotate i j = s (~ i) (~ j)

  diagonal : a ≡ b
  diagonal i = s i i

module ConstructionOfSquares
  (a b : A)
  (diag : a ≡ b)
  where

  s : (λ i → diag i ≡ b) [ diag ≡ refl {x = b} ]
  s i j = diag (i ∨ j)
