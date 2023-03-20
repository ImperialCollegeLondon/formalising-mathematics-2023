/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import number_theory.number_field.class_number
import tactic

/-

# Class groups

In Lean we don't talk about the class group of a number field, we talk about
the class group of its integer ring. 

-/

variables (R : Type) [comm_ring R] [is_domain R]

example : Type := class_group R

noncomputable example : comm_group (class_group R) := infer_instance

/-

So what is this group?

A *fractional ideal* of `R` is an `R`-submodule `J` of the field of fractions of `R`
such that there exists a nonzero element `a` of `R` such that `a * J ⊆ R`.

-/

open_locale non_zero_divisors -- to get notation R⁰ for the submonoid of nonzero divisors of R
-- (of course in this case it's just R \ {0}).

-- the fractional ideals of R
example : Type := fractional_ideal (R⁰) (fraction_ring R)

-- Note that (0) is a fractional ideal with this definition. So fractional ideals aren't
-- a group under multiplication, only a monoid.

example : comm_monoid (fractional_ideal (R⁰) (fraction_ring R)) := infer_instance

-- However the invertible fractional ideals (for a number field this is the same as the
-- nonzero fractional ideals) are a group:

example : comm_group (fractional_ideal (R⁰) (fraction_ring R))ˣ := infer_instance

-- There's a group homomorphism from the units of `fraction_ring R` to the invertible
-- fractional ideals

noncomputable example : 
  (fraction_ring R)ˣ →* (fractional_ideal (R⁰) (fraction_ring R))ˣ := 
to_principal_ideal R _

-- And the class group of `R` is defined to be the quotient of the invertible fractional
-- ideals by the image of this map.

example : class_group R =
  ((fractional_ideal R⁰ (fraction_ring R))ˣ ⧸ (to_principal_ideal R (fraction_ring R)).range) := rfl

-- For a general integral domain, the class group may be infinite. But the class group
-- of the integers of a number field is known by Lean to be finite.

open number_field

noncomputable example (K : Type) [field K] [number_field K] : 
  fintype (class_group (ring_of_integers K)) :=
infer_instance

-- Proved in 2021 in Lean. See https://arxiv.org/abs/2102.02600 to see how it was done. 
-- My PhD student Ashvni Narayanan was one of the people involved in the proof. 
