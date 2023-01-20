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
-- of a group?

example (a b c : G) : (a * b) * c = a * (b * c) :=
begin
  sorry
end

example (a : G) : a * 1 = a :=
begin
  sorry
end

-- Can you guess the last two?
example (a : G) : 1 * a = a :=
begin
  sorry
end

example (a : G) : a * a⁻¹ = 1 :=
begin
  sorry
end

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.

-- let a,b,c be elements of G in the below.
variables (a b c : G)


example : a⁻¹ * (a * b) = b :=
begin
  sorry
end

example : a * (a⁻¹ * b) = b :=
begin
  sorry
end

example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c :=
begin
  -- hint for this one : `b * (a * c) = (b * a) * c`
  sorry,
end

example : a * b = 1 ↔ a⁻¹ = b :=
begin
  sorry,
end

example : (1 : G)⁻¹ = 1 :=
begin
  sorry,
end

example : (a⁻¹)⁻¹ = a :=
begin
  sorry,
end

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := 
begin
  sorry,
end

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `library_search` or by
educated guessing).

-/

example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 :=
begin
  group,
end

-- Try this: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g :=
begin
  sorry
end
