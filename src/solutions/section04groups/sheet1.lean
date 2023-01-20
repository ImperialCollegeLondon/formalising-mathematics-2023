/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-

# Groups

## How to use Lean's groups

In previous courses I have made groups from scratch, but it's kind of irritating
to do (because all the lemma names like `mul_one` are already taken) and I'm
not entirely sure that most students want to know how to make their own
groups, rings, whatever: what's the point if these things are there already?

So in this sheet I explain how to use Lean's groups.

-/

-- let G be a group
variables (G : Type) [group G]

-- Let's see what just happened.
example (g : G) : g⁻¹ * g = 1 :=
begin
  /- The tactic state now looks like this:
  
  G : Type
  _inst_1 : group G
  g : G
  ⊢ g⁻¹ * g = 1
  
  So G is what most mathematicians would call a "set", and what in this course
  we call a "type" (they're the same thing as far as you're concerned), and
  `g : G` just mean "g is an element of G". The remaining thing is this 
  `_inst_1` thing, and that means "G has a multiplication `*`, an identity `1`,
  an inverse function `⁻¹`, and satisfies all the group axioms; furthermore
  all of this will be taken care of by "instances", which are a part
  of Lean's "type class inference system". The type class inference system
  is the system which deals with stuff in square brackets. You don't have
  to worry about it right now -- all that matters is that you have access
  to all the group axioms. This one is called `inv_mul_self g`. 
  -/
  exact inv_mul_self g,
end

-- Why don't you use `library_search` to see the names of the other axioms
-- of a group? Note that when `library_search` has run, you can click on
-- the output (the blue output in the infoview) and replace `library_search`
-- with the name of the axiom it found. Note also that you can instead *guess*
-- the names of the axioms. For example what do you think the proof of `1 * a = a` is called?

example (a b c : G) : (a * b) * c = a * (b * c) :=
begin
  exact mul_assoc a b c, -- can be found with `library_search` if you didn't know the answer already
end

example (a : G) : a * 1 = a :=
begin
  exact mul_one a,
end

-- Can you guess the last two?
example (a : G) : 1 * a = a :=
begin
  exact one_mul a
end

example (a : G) : a * a⁻¹ = 1 :=
begin
  exact mul_inv_self a
end

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.

-- let a,b,c be elements of G in the below.
variables (a b c : G)

-- inv_mul_cancel_left
example : a⁻¹ * (a * b) = b :=
begin
  rw [← mul_assoc, inv_mul_self, one_mul],
end

-- mul_inv_cancel_left
example : a * (a⁻¹ * b) = b :=
begin
  rw [← mul_assoc, mul_inv_self, one_mul]
end

-- left_inv_eq_right_inv
example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c :=
begin
  have h : b * (a * c) = (b * a) * c,
  { rw mul_assoc, },
  rwa [h1, h2, mul_one, one_mul] at h,
end

-- mul_eq_one_iff_inv_eq
example : a * b = 1 ↔ a⁻¹ = b :=
begin
  split,
  { intro h,
    exact left_inv_eq_right_inv (inv_mul_self a) h, },
  { rintro rfl,
    exact mul_inv_self a, },
end

-- inv_one
example : (1 : G)⁻¹ = 1 :=
begin
  rw [← mul_eq_one_iff_inv_eq, mul_one],
end

-- inv_inv
example : (a⁻¹)⁻¹ = a :=
begin
  rw [← mul_eq_one_iff_inv_eq, inv_mul_self],
end

-- mul_inv_rev
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := 
begin
  rw [← mul_eq_one_iff_inv_eq, ← mul_assoc, mul_assoc a, mul_inv_self, mul_one, mul_inv_self],
end

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above; a theorem of Knuth and Bendix
says that these examples and the axioms of a group give a "confluent rewrite system"
which can solve any identity in group theory. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `library_search` or by
educated guessing).

-/

example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 :=
begin
  rw [inv_one, inv_one, mul_one, mul_inv_rev, inv_inv, inv_inv, mul_assoc, mul_assoc, mul_assoc,
      mul_inv_cancel_left, mul_assoc, mul_inv_cancel_left, inv_mul_self],
end

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g :=
begin
  have useful : ∀ g : G, g = g⁻¹,
  { intro g,
    rw [← eq_comm, ← mul_eq_one_iff_inv_eq],
    exact h g, },
  intros g h,
  rw [useful (g * h), mul_inv_rev, ← useful g, ← useful h],
end
