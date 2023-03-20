/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import data.real.basic

import number_theory.number_field.class_number
import tactic
/-

# Number fields and their rings of integers.

## A subtlety about fields of fractions.

Here's a question: is ℚ *equal* to the field of fractions of ℤ? Not in Lean. Of course
they're (canonically) isomorphic. But they're not identical.

The algebraic number theory course at Imperial is focussed on number fields and their
rings of integers. But note that if you start with a number field, take its ring
of integers, and then take the field of fractions, then you only recover an isomorphic
number field. Similarly if you start with a ring of integers, take its field of fractions
and then take the algebraic integers in this number field, you only recover an isomorphic
ring of integers.

Lean fixes this problem by having *two* ways to talk about fields of fractions. The
first one is `fraction_ring`. This constructs *data*. If you start with an integral
domain `R` then `fraction_ring R` is a type, equipped with a field structure and
a ring homomorphism from `R`, and it's the field of fractions of `R`. Let's see this in action.

-/

namespace examples

 -- cheap way of generating ℤ[i]: the subring of ℂ generated by `i`.  
@[derive [comm_ring, is_domain]]
def R : Type := (subring.closure {complex.I} : subring ℂ) 

-- The `derive` thing is just to make this work:
example : comm_ring R := infer_instance
example : is_domain R := infer_instance

-- Now let's make ℚ(i) as the field of fractions of ℤ[i]
@[derive field]
def K : Type := fraction_ring R 

end examples

/-
So that's one way to make number fields. But it's not a convenient way.
For example, lean already has ℚ so you wouldn't want to re-make it as
`fraction_ring ℤ`; it wouldn't be possible to prove that this new version
of ℚ was *equal* to ℚ, you could only prove it's isomorphic, and then
you'd have to carry around the isomorphism. We fix this in `mathlib`
by having a second definition, `is_fraction_ring`. What is this?

The point is that although we say "the" field of fractions of an
integral domain, these things are defined as quotients and
are hence only unique up to unique isomorphism. It is possible
to make many types `A` which are isomorphic to ℚ. Only one of them
will be *equal* to `fraction_ring ℤ`. But all of them will
satisfy the proposition `is_fraction_ring ℤ A`.

-/

-- works fine
example : is_fraction_ring ℤ ℚ :=
begin
  exact rat.is_fraction_ring, -- thanks `library_search`
end

example : fraction_ring ℤ = ℚ := sorry -- *NOT PROVABLE IN LEAN*
-- because `fraction_ring ℤ` is some kind of quotient of
-- pairs (a,b) with b≠0 by some equivalence relation, whereas ℚ is 
-- not a quotient, it's internally defined to be 
-- pairs (a,b) with a : ℤ, b : ℕ, 0 < b and gcd(a,b)=1. 

-- Of course the fraction ring satisfies `is_fraction_ring` though!

example 
  -- let R be an integral domain
  (R : Type) [comm_ring R] [is_domain R] :
  -- Then `fraction_ring R` satisfies `is_fraction_ring R _`.
  is_fraction_ring R (fraction_ring R) :=
begin
  exact localization.is_localization
end

-- In fact `is_fraction_ring` is a class, so this works too:

example (R : Type) [comm_ring R] [is_domain R] : is_fraction_ring R (fraction_ring R) := infer_instance

/-

The first proof indicates that actually this `fraction_ring` / `is_fraction_ring` story is just
a special case of a more general `localization` / `is_localization` story, where you
can either choose to localise a commutative ring `R` at a multiplicative subset `S`, or say
that a given `R`-algebra `A` is a localisation of `R` at `S`, in the sense that
it satisfies the universal property.

## How to make a number field

-/

-- This says "let K be a number field"
variables (K : Type) [field K] [number_field K]

/-

## How to make its integers

-/

open number_field 

-- This is how to make its ring of integers: note that it's a term, not a type.
example : subalgebra ℤ K := ring_of_integers K

-- If you look at the definition of `ring_of_integers` you'll see that it's just this:
-- `def ring_of_integers := integral_closure ℤ K`

-- There's notation for this construction in the `number_field` locale

open_locale number_field

example : subalgebra ℤ K := 𝓞 K

-- The library has the theorem that a number field is a field of fractions
-- of its integer ring:
example : is_fraction_ring (𝓞 K) K := 
begin
  -- Goal is the below; note the coercion from the subalgebra to a type.
  -- `⊢ is_fraction_ring ↥(𝓞 K) K`
  exact ring_of_integers.is_fraction_ring,
end

/-

## `integral_closure` and `is_integral_closure`

Just as `ℚ` was not *equal* to the field of fractions of `ℤ`, `ℤ` is
not *equal* to the integer ring of `ℚ` in Lean.

-/

example : ℤ = 𝓞 ℚ := sorry -- *NOT PROVABLE*.


/-

However, just as in the field of fractions case, we have a workaround.

Just as `ring_of_integers` is a concrete construction, and a special case
of the concrete construction `integral_closure`, there is a proposition
`is_integral_closure A R K`, for `K` an `R`-algebra and an `A`-algebra,
saying that `A` is the integral closure of `R` (within `K`).
Unsurprisingly, the `integral_closure` satisfies `is_integral_closure`.

-/

example : is_integral_closure (𝓞 K) ℤ K := 
begin
  exact ring_of_integers.is_integral_closure
end

-- But also unsurprisingly, other rings do too.

example : is_integral_closure ℤ ℤ ℚ := 
begin
  exact is_integrally_closed.is_integral_closure
end

-- Like `is_fraction_ring`, `is_integral_closure` is a class, so this works too:

example : is_integral_closure (𝓞 K) ℤ K := infer_instance
example : is_integral_closure ℤ ℤ ℚ := infer_instance


/-

## Examples

So that was a bunch of abstract nonsense. What about "the integers of ℚ(√2) are ℤ[√2]"?
I'm not sure Lean has any examples! This might make an interesting project.

Here's one way to make ℚ(√2)

-/

open_locale polynomial -- for A[X] notation
open polynomial -- so I can say `X` instead of `polynomial.X` 

@[derive comm_ring]
def K' : Type := ℚ[X] ⧸ (ideal.span ({X^2 - 2} : set (ℚ[X])))

noncomputable example : comm_ring K' := 
begin
  apply_instance,
end

/- 

But you can't `derive field` because the type class inference system doesn't
know that X^2-2 is irreducible. So now you have to prove K is a field (the
easiest way would be to prove that the ideal was maximal) and then
prove it's a number field. This is definitely do-able.

Here's a totally different approach:

-/

structure Q_sqrt_2 : Type :=
(r : ℚ) 
(i : ℚ) 
-- idea is that this models r+i√2

namespace Q_sqrt_2

def add (a b : Q_sqrt_2) : Q_sqrt_2 :=
{ r := a.r + b.r,
  i := a.i + b.i }

instance : has_add Q_sqrt_2 := ⟨add⟩

def mul (a b : Q_sqrt_2) : Q_sqrt_2 :=
{ r := a.r * b.r + 2 * a.i + b.i,
  i := a.r * b.i + a.i * b.r, }

instance : has_mul Q_sqrt_2 := ⟨mul⟩

-- etc etc. Probably the work here is easier but there's more of it (Lean doesn't even
-- know that `Q_sqrt_2` is an additive group, let alone a field)

-- As an exercise, try proving that `Q_sqrt_2` is an `add_comm_group` (you'll need to define `zero` and `neg`),
-- and then a ring, and then a field, and then a number field. 

@[simp] lemma add_r (a b : Q_sqrt_2) : (a + b).r = a.r + b.r := rfl
@[simp] lemma add_i (a b : Q_sqrt_2) : (a + b).i = a.i + b.i := rfl

@[ext]
lemma ext (a b : Q_sqrt_2) (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := by cases a; cases b; simp * at *

instance : has_zero Q_sqrt_2 := ⟨⟨0,0⟩⟩
@[simp] lemma zero_r : (0 : Q_sqrt_2).r = 0 := rfl
@[simp] lemma zero_i : (0 : Q_sqrt_2).i = 0 := rfl

instance : has_neg Q_sqrt_2 := ⟨λ x, ⟨-x.1, -x.2⟩⟩ 
@[simp] lemma neg_r (a : Q_sqrt_2) : (-a).r = -(a.r) := rfl
@[simp] lemma neg_i (a : Q_sqrt_2) : (-a).i = -(a.i) := rfl

instance : add_comm_group Q_sqrt_2 := 
{ add := (+),
  add_assoc := by rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩; ext; simp [add_assoc],
  zero := 0,
  zero_add := by rintro ⟨_, _⟩; ext; simp,
  add_zero := by rintro ⟨_, _⟩; ext; simp,
  neg := has_neg.neg,
  add_left_neg := by rintro ⟨_, _⟩; ext; simp,
  add_comm := by rintro ⟨_, _⟩ ⟨_, _⟩; ext; simp [add_comm] }
end Q_sqrt_2

-- etc etc
-- For hints, see the complex number game repository, where I build ℂ from ℝ.
