module part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Nat using (zero; suc; _+_) renaming (Nat to ℕ)

add_suc_eq_suc_add : ∀ (a b : ℕ) -> a + suc b ≡ suc (a + b)
add_suc_eq_suc_add 0 b = refl
add_suc_eq_suc_add (suc a) b =
  begin
    suc a + suc b
  ≡⟨⟩
    suc (a + suc b)
  ≡⟨ cong suc (add_suc_eq_suc_add a b) ⟩
    refl

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

to : ℕ → Bin
to zero = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (n O) = from n + from n
from (n I) = suc (from n) + from n

from_inc_eq_suc_from : ∀ (n : Bin) → from (inc n) ≡ suc (from n)
from_inc_eq_suc_from ⟨⟩ = refl
from_inc_eq_suc_from (n O) = refl

from_inc_eq_suc_from (n I) =
  begin
    from (inc (n I))
  ≡⟨⟩
    from (inc n) + from (inc n)
  ≡⟨ cong (λ { m → m + m }) (from_inc_eq_suc_from n) ⟩
    suc (from n) + suc (from n)
  ≡⟨ add_suc_eq_suc_add (suc (from n)) (from n) ⟩
    refl

from_to_eq_id : ∀ (n : ℕ) → from (to n) ≡ n
from_to_eq_id zero = refl
from_to_eq_id (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ from_inc_eq_suc_from (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from_to_eq_id n) ⟩
    suc n
  ∎
