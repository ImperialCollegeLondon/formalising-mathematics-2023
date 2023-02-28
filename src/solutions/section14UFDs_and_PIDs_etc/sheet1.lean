/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import ring_theory.principal_ideal_domain -- theory of PIDs

/-

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/

variables (R : Type) [comm_ring R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain. 
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":

variables [is_principal_ideal_ring R] [is_domain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.

example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 :=
begin
  intros a b,
  apply eq_zero_or_eq_zero_of_mul_eq_zero, -- typeclass inference 
  -- magically extracts the assumption from `is_domain`
end

example : (0 : R) ≠ 1 :=
begin
  -- this is another consequence of being an integral domain
  apply zero_ne_one,
end

example (I : ideal R) : I.is_principal :=
begin
  -- typeclass inference system finds `is_principal_ideal_ring` and
  -- uses it automatically
  exact is_principal_ideal_ring.principal I,
end

example (I : ideal R) : ∃ j, I = ideal.span {j} :=
begin
  -- to make a term of type `is_principal I` you need to give one proof,
  -- but we still need to do `cases` or equivalent (I used `obtain` below)
  -- to get this proof out.
  obtain ⟨h⟩ := is_principal_ideal_ring.principal I,
  exact h,
end
