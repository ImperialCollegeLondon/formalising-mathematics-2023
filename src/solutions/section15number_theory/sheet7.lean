/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic

/-

# Prove that for every positive integer n the number 3(1^5 +2^5 +...+n^5)
# is divisible by 1^3+2^3+...+n^3

This is question 9 in Sierpinski's book

-/

open_locale big_operators

open finset

-- I knew this one
lemma sum_cubes (n : ℕ) : ∑ i in range n, (i : ℚ)^3 = (n*(n-1)/2)^2 :=
begin
  induction n with d hd,
  { simp, },
  { rw [finset.sum_range_succ, hd],
    simp,
    ring }
end

-- I looked this one up on Wikipedia
lemma sum_fifths (n : ℕ) : ∑ i in range n, (i : ℚ)^5 = (4 * (n * (n-1)/2)^3-(n*(n-1)/2)^2)/3 :=
begin
  induction n with d hd,
  { simp, },
  { rw [finset.sum_range_succ, hd],
    simp,
    ring }
end

example (n : ℕ) : (∑ i in range n, i^3) ∣ (3 * ∑ i in range n, i^5) :=
begin
  rw ← int.coe_nat_dvd,
  use 2 * n * (n-1) - 1, -- I used a computer algebra package to work out the ratio
  rw ← @int.cast_inj ℚ _ _ _ _,
  push_cast,
  rw sum_cubes,
  rw sum_fifths,
  ring,
end

