/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import number_theory.divisors -- added to make Bhavik's proof work

namespace section15sheet2solutions
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
  have h : x - 3 ∣ x ^ 3 - 27,
  { use x ^ 2 + 3 * x + 9,
    ring, },
  split,
  { intro h1,
    have h2 := dvd_sub h1 h,
    convert h2,
    ring },
  { intro h1,
    convert dvd_add h h1,
    ring },
end

lemma int_dvd_iff (x : ℤ) (n : ℤ) (hn : n ≠ 0) :
  x ∣ n ↔ x.nat_abs ∈ n.nat_abs.divisors :=
by simp [hn]

-- Thanks to Bhavik Mehta for showing me how to prove this in Lean 3 without timing out!
lemma lemma2 (x : ℤ) : x ∣ 24 ↔ x ∈ ({-24,-12,-8,-6,-4,-3,-2,-1,1,2,3,4,6,8,12,24} : set ℤ) :=
begin
  suffices : x ∣ 24 ↔ x.nat_abs ∈ ({1,2,3,4,6,8,12,24} : finset ℕ),
  { simp only [this, int.nat_abs_eq_iff, set.mem_insert_iff, set.mem_singleton_iff,
      finset.mem_insert, finset.mem_singleton],
    norm_cast,
    rw ←eq_iff_iff,
    ac_refl },
  exact int_dvd_iff _ 24 (by norm_num),
end

-- This seems much harder :-) (it's really a computer science question, not a maths question,
-- feel free to skip)
example (x : ℤ) : x - 3 ∣ x^3 - 3 ↔ x ∈ ({-21, -9, -5, -3, -1, 0, 1, 2, 4, 5, 6, 7, 9, 11, 15, 27} : set ℤ)  :=
begin
  rw lemma1,
  rw lemma2,
  simp only [set.mem_insert_iff, sub_eq_neg_self, set.mem_singleton_iff],
  repeat {apply or_congr },
  all_goals { omega },
end

end section15sheet2solutions