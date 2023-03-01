/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import algebra.euclidean_domain.instances
import data.polynomial.field_division -- polynomial rings over a field are EDs
/-

# Euclidean Domains

Lean's definition of a Euclidean domain is more general than the usual one presented
to undergraduates. First things first: here's how to say "let R be a Euclidean domain"

-/

variables (R : Type) [euclidean_domain R]

/-

And there's various theorems (all known by the typeclass inference system) about
Euclidean domains:

-/

example : euclidean_domain ℤ := by apply_instance

open_locale polynomial

-- I neither know nor care why it's noncomputable, but it doesn't matter to mathematicians
noncomputable example (k : Type) [field k] : euclidean_domain k[X] := infer_instance

-- Euclidean domains are PIDs
example (R : Type) [euclidean_domain R] : is_principal_ideal_ring R := infer_instance
example (R : Type) [euclidean_domain R] : is_domain R := infer_instance

/-

Internally the definition of a Euclidean domain is this. It's a ring with the following
structure/axioms:

1) You have a "quotient" function `quotient r s` and a remainder function `remainder r s`,
both of type `R → R → R` (i.e. functions from `R²` to `R`) 

2) You have an axiom saying `∀ a b, a = b * quotient a b + remainder a b`

3) You have a binary relation `≺` on the ring such that `remainder a b ≺ b`

4) You have an axiom saying that `≺` is well-founded, i.e., there are no infinite decreasing
sequences.

The point is that these axioms are enough to get Euclid's algorithm to work.

In usual maths you have a function from `R` to `ℕ` sending an element `b` to its "size",
and an axiom saying that the remainder when you divide something by `b` is sent to a smaller
natural number. In Lean the natural numbers are not involved; all that we guarantee is
that you can't keep taking remainders infinitely often, which turns out to be a very slightly
weaker statement. Let's prove that any "normal" Euclidean domain is a mathlib Euclidean domain.

-/

open_locale classical

noncomputable example (R : Type) [comm_ring R] [is_domain R] (φ : R → ℕ) 
  (h : ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ φ r < φ b)) 
  (h0 : ∀ a b : R, a ≠ 0 → b ≠ 0 → φ a ≤ φ (a * b)) : 
  euclidean_domain R :=
begin
  let φ' : R → ℕ := λ r, if r = 0 then 0 else 1 + φ r, 
  have h' : ∀ a b : R, ∃ q r : R, a = b * q + r ∧ ((b = 0 ∧ q = 0 ∧ r = a) ∨ (b ≠ 0 ∧ φ' r < φ' b)),
  { intros a b,
    by_cases hb : b = 0,
    { use [0,a, by simp],
      left, exact ⟨hb, rfl, rfl⟩, },
    { rcases h a b hb with ⟨q, r, h1, h2⟩,
      use [q, r, h1],
      right,
      refine ⟨hb, _⟩, 
      cases h2 with h2 h2,
      { simp [φ'],
        rw if_pos h2,
        rw if_neg hb,
        linarith, },
      { simp [φ'],
        rw if_neg hb,
        split_ifs,
        { linarith },
        { linarith }, }, }, },
  choose quot rem h'' using h',
  exact
{ quotient := quot,
  quotient_zero := begin
    intro a,
    cases h'' a 0 with _ h1,
    cases h1,
    { exact h1.2.1, },
    { cases h1 with h1 h2, exfalso, apply h1, refl, },
  end,
  remainder := rem,
  quotient_mul_add_remainder_eq := begin
    intros a b,
    rw ← (h'' a b).1,
  end,
  r := λ a b, φ' a < φ' b,
  r_well_founded := begin
    apply inv_image.wf,
    exact is_well_founded.wf,
  end,
  remainder_lt := begin
    intros a b hb,
    rcases h'' a b with ⟨h1, ⟨h2, -⟩ | h3⟩,
    { contradiction },
    exact h3.2,
  end,
  mul_left_not_lt := begin
    intros a b hb,
    push_neg,
    by_cases ha : a = 0,
    { simp [φ'],
      subst ha,
      simp, },
    { specialize h0 a b ha hb,
      simp [φ'],
      rw if_neg ha,
      split_ifs with hab hab,
      { exfalso, 
        revert hab,
        exact mul_ne_zero ha hb,
      },
      { linarith, } },
  end },
end
