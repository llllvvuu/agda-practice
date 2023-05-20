{-# OPTIONS --cubical #-}
module HITs where
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Nat using (Nat; suc; zero) renaming (_+_ to _⊕_)
open import Function.Base using (_|>_)

variable A : Set

data Int : Set where
  pos : Nat → Int
  neg : Nat → Int
  zro : pos 0 ≡ neg 0

succ : Int → Int
succ (pos x) = pos (suc x)
succ (neg zero) = pos 1
succ (neg (suc x)) = neg x
succ (zro i) = pos 1

pred : Int → Int
pred (pos zero) = neg 1
pred (pos (suc x)) = pos 0
pred (neg x) = neg (suc x)
pred (zro i) = neg 1

module IsoInt where
  open import Cubical.Data.Int using () renaming (ℤ to StdInt)
  pattern spos n = StdInt.pos n
  pattern nsuc n = StdInt.negsuc n

  StdInt→Int : StdInt → Int
  StdInt→Int (spos n) = pos n
  StdInt→Int (nsuc n) = neg (suc n)

  Int→StdInt : Int → StdInt
  Int→StdInt (pos n) = spos n
  Int→StdInt (neg (suc n)) = nsuc n
  Int→StdInt (neg 0) = spos 0
  Int→StdInt (zro i) = spos 0

  StdInt→Int→StdInt : ∀ (n : StdInt) → (n |> StdInt→Int |> Int→StdInt) ≡ n
  StdInt→Int→StdInt (spos n) = refl
  StdInt→Int→StdInt (nsuc n) = refl

  Int→StdInt→Int : ∀ (n : Int) → (n |> Int→StdInt |> StdInt→Int) ≡ n
  Int→StdInt→Int (pos n) = refl
  Int→StdInt→Int (neg 0) = zro
  Int→StdInt→Int (neg (suc n)) = refl
  Int→StdInt→Int (zro i) j = zro (i ∧ j)

  Int≡StdInt = isoToPath (iso Int→StdInt
                              StdInt→Int
                              StdInt→Int→StdInt
                              Int→StdInt→Int)

infixl 5 _⊝_
data DeltaInt : Set where
  _⊝_    : Nat -> Nat -> DeltaInt
  cancel : ∀ a b -> a ⊝ b ≡ suc a ⊝ suc b

dsuc : DeltaInt → DeltaInt
dsuc (a ⊝ b) = (suc a) ⊝ b
dsuc (cancel a b i) = cancel (suc a) b i

dpred : DeltaInt → DeltaInt
dpred (a ⊝ b) = a ⊝ (suc b)
dpred (cancel a b i) = cancel a (suc b) i

infixl 5 _+_
_+_ : DeltaInt → DeltaInt → DeltaInt
(a ⊝ b) + (c ⊝ d) = (a ⊕ c) ⊝ (b ⊕ d)
(cancel a b i) + (c ⊝ d) = cancel (a ⊕ c) (b ⊕ d) i
(a ⊝ b) + (cancel c d j) = ? -- cancel (a ⊕ c) (b ⊕ d) j
(cancel a b i) + (cancel c d j) = ? -- (a ⊕ c) ⊝ (b ⊕ d)
