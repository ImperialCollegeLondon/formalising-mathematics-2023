/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import number_theory.divisors -- added to make Bhavik's proof work

/-

# Find all integers x ≠ 3 such that x - 3 divides x^3 - 3

This is the second question in Sierpinski's book "250 elementary problems
in number theory".

My solution: x - 3 divides x^3-27, and hence if it divides x^3-3
then it also divides the difference, which is 24. Conversely,
if x-3 divides 24 then because it divides x^3-27 it also divides x^3-3.
But getting Lean to find all the integers divisors of 24 is a nightmare!
Bhavik (last year) managed to figure out how to do this.

-/

-- This isn't so hard
lemma lemma1 (x : ℤ) : x - 3 ∣ x^3 - 3 ↔ x - 3 ∣ 24 :=
begin
  sorry,
end

-- This seems much harder :-) (it's really a computer science question, not a maths question,
-- and probably you'll have to properly understand what Lean does quickly and
-- slowly in order to do it, feel free to skip)
example (x : ℤ) : x - 3 ∣ x^3 - 3 ↔ x ∈ ({-21, -9, -5, -3, -1, 0, 1, 2, 4, 5, 6, 7, 9, 11, 15, 27} : set ℤ)  :=
begin
  sorry,
end

