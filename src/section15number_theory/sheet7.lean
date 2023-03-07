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

example (n : ℕ) : (∑ i in range n, i^3) ∣ (3 * ∑ i in range n, i^5) :=
begin
  sorry,
end

