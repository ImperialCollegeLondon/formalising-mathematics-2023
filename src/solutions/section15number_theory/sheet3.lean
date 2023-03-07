/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic

/-

# Prove that there exists infinitely many positive integers n such that
# 4n² + 1 is divisible both by 5 and 13.

This is the third question in Sierpinski's book "250 elementary problems
in number theory".

Maths proof: if n=4 then 4n^2+1=65 is divisible by both 5 and 13
so if n is congruent to 4 mod 5 and mod 13 (i.e if n=4+65*t)
then this will work.

There are various ways to formalise the statement that some set
of naturals is infinite. We suggest two here (although proving
they're the same is fiddly)

-/

-- The number-theoretic heart of the argument.
-- Note that "divides" is `\|` not `|`
lemma divides_of_cong_four (t : ℕ) : 5 ∣ 4 * (65 * t + 4)^2 + 1 ∧
13 ∣ 4 * (65 * t + 4)^2 + 1 :=
begin
  split,
  { use 3380*t^2 + 416*t + 13,
    ring },
  { use 1300*t^2 + 160*t + 5,
    ring }
end

-- There are arbitrarily large solutions to `5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1`
lemma arb_large_soln : ∀ N : ℕ, ∃ n > N, 5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1 :=
begin
  intro N,
  -- need to find t such that 65t+4>N. Just set t=N for simplicity
  use 65 * N + 4,
  split,
  { linarith },
  { apply divides_of_cong_four }  
end

-- This is not number theory any more, it's switching between two
-- interpretations of "this set of naturals is infinite" 
lemma infinite_iff_arb_large (S : set ℕ) : S.infinite ↔ ∀ N, ∃ n > N, n ∈ S :=
begin
  split,
  { intro h,
    have h2 := set.infinite.exists_nat_lt h,
    intro n,
    rcases h2 n with ⟨m, hm, h3⟩,
    use m,
    exact ⟨h3, hm⟩,
  },
  { contrapose!,
    intro h,
    rw set.not_infinite at h,
    let S2 : finset ℕ := set.finite.to_finset h,
    have h2 : ∃ B, ∀n ∈ S2, n ≤ B,
    { use finset.sup S2 id,
      intros,
      apply finset.le_sup H },
    cases h2 with N hN,
    use N,
    have h3 : ∀n : ℕ, n ∈ S ↔ n ∈ S2,
      intro n,
      exact (set.finite.mem_to_finset h).symm,
    intros n hn h4,
    rw h3 at h4,
    specialize hN n h4,
    linarith,
  }
end

-- Another way of stating the question (note different "|" symbols:
-- there's `|` for "such that" in set theory and `\|` for "divides" in number theory)
lemma infinite_set_of_solutions : {n : ℕ | 5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1}.infinite :=
begin
  rw infinite_iff_arb_large,
  exact arb_large_soln,
end
