{-# OPTIONS --cubical #-}
module Paths&Intervals where

open import Cubical.Core.Everything

congruence :
  {ℓ : Level}
  {A B : Set}
  {a b : A}
  (f : A → B) (p : a ≡ b) → f a ≡ f b
congruence f p i = f (p i)

functionExtensionality :
  {ℓ : Level}
  {A B : Set}
  {f : A → B}
  {g : A → B}
  (p : ∀ a → f a ≡ g a) → f ≡ g
functionExtensionality p i a = p a i
