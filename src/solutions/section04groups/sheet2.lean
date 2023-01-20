/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Challenge sheet

This is a harder group theory question. 

It turns out that two of the axioms in our definition of a group
are not needed; they can be deduced from the others. Let's define
a "weak group" class, where we only have three of the group axioms.
The question is: can you prove that a weak group is a group, by
proving the other axioms?

-/

-- removing `mul_one` and `mul_inv_self` from the five standard axioms
-- for a group. 
class weak_group (G : Type) extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)

namespace weak_group

variables {G : Type} [weak_group G] (a b c : G)


/-

The challenge is to prove that G is a group, which we can interpret as
proving the missing axioms `mul_one` and `mul_inv_self`. Note that you
can't use the `group` tactic any more because `G` isn't a group yet:
this is what you're trying to prove!

One way of doing it: try proving 

`mul_left_cancel : a * b = a * c → b = c`

and then

`mul_eq_of_eq_inv_mul : b = a⁻¹ * c → a * b = c`

first.

-/

-- proof using cool `calc` mode
lemma mul_left_cancel (h : a * b = a * c) : b = c :=
calc
  b = 1 * b         : by rw one_mul
... = (a⁻¹ * a) * b : by rw inv_mul_self
... = a⁻¹ * (a * b) : by rw mul_assoc
... = a⁻¹ * (a * c) : by rw h
... = (a⁻¹ * a) * c : by rw mul_assoc
... = 1 * c         : by rw inv_mul_self
... = c             : by rw one_mul

lemma mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c :=
begin
  apply mul_left_cancel a⁻¹,
  rwa [← mul_assoc, inv_mul_self, one_mul],
end

lemma mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw inv_mul_self,
end

lemma mul_inv_self (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

end weak_group

/-

If you want to take this further: prove that if we make
a new class `bad_group` by replacing
`one_mul` by `mul_one` in the definition of `weak_group`
then it is no longer true that you can prove `mul_inv_self`;
there are structures which satisfy `mul_assoc`, `mul_one`
and `inv_mul_self` but which really are not groups.
Can you find an example? Try it on paper first. 

-/

-- claim: not a group in general
class bad_group (G : Type)
  extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(mul_one : ∀ a : G, a * 1 = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)

instance : has_one bool := ⟨bool.tt⟩
instance : has_mul bool := ⟨λ x y, x⟩
instance : has_inv bool := ⟨λ x, 1⟩

instance : bad_group bool :=
{ mul_assoc := dec_trivial,
  mul_one := dec_trivial,
  inv_mul_self := dec_trivial,
}

example : ¬ (∀ a : bool, 1 * a = a) :=
begin
  dec_trivial,
end
