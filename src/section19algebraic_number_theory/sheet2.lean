/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import data.real.basic

import number_theory.number_field.class_number
import tactic

namespace section19sheet2
/-

# More on rings of integers.

Lean has a lot of commutative algebra machinery in its maths library. For example it knows
that the set of elements of a number field which are integral over ℤ form a ring; the fact
that the sum of two integral elements is integral is not obvious. Here is a high-powered
conceptual proof formalised in Lean. Note that the version in Lean's maths library of this
proof was written by an Imperial undergrad!

-/


variables (K : Type) [comm_ring K] -- [number_field K] -- not actually necessary for this sheet

-- The key lemma (proved in mathlib already):
-- An element of K is integral over a subring R iff the subring ℤ[a] of K is finitely-generated
-- as a ℤ-module (i.e. as an abelian group)
lemma lemma1 (R : Type) [comm_ring R] [algebra R K] (a : K) : 
  is_integral R a ↔ (algebra.adjoin R ({a} : set K)).to_submodule.fg :=
begin
  split,
  -- Both directions are delicate to do in Lean, but there already
  { exact fg_adjoin_singleton_of_integral a, },
  { intro h,
    exact is_integral_of_mem_of_fg _ h _ (algebra.self_mem_adjoin_singleton R a),
  },
end

-- One can use this lemma to prove that if `a` and `b` are integral then `R[a]` is finitely-generated
-- as an R-module, and `R[a][b]` is finitely-generated as an R[a]-module, so finitely-generated
-- as an `R`-module. If furthermore `R` is Noetherian (for example `R=ℤ` then the subalgebras `R[a+b]` and `R[ab]`
-- are finitely-generated as `R`-modules, so by the lemma applied the other way we deduce
-- that these elements are integral. This is still a hard exercise (despite the lemma)
-- because you have to move between `R` and `R[a]`. 

example (a b : K) (ha : is_integral ℤ a) (hb : is_integral ℤ b) : is_integral ℤ (a + b) :=
begin
  sorry -- I don't finish this in the solutions
end

end section19sheet2