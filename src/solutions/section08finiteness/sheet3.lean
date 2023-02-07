/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic

/-

# Finite types

As well as finite subsets of a (possibly infinite type), Lean has a theory
of finite types. Just like finite subsets, there is a `Prop`-valued version
(the true-false statement "this type is finite") and a `Type`-valued version 
("here is an explicit list of all the finitely many terms of this type").
If you want to work constructively, then use the `Type` version, and if
you just care about theorems you can use the `Prop` version.

## The Prop-valued version

If `(X : Type)` then `finite X` is the true-false statement saying
that `X` is finite. It's a class, which means it goes in square brackets.

-/

section prop_version

-- Let X be a finite type
variables (X : Type) [finite X]

-- The typeclass inference system now knows that various other types are finite:

variables (Y : Type) [finite Y]

example : finite (X × Y) := infer_instance
example : finite (X → Y) := infer_instance

-- The type `fin n` is a structure. To make a term of this structure
-- you need to give a natural `a`, and a proof that `a < n`.

example : fin 37 := ⟨3, by linarith⟩

-- The typeclass inference system also knows that these are finite

example : finite (fin 37) := infer_instance

end prop_version

/-

## The Type-valued version

This is `[fintype X]`. It's (in my opinion) harder to use, but finite sums work
for it, and they don't appear to work for `finite`.

-/

-- Let X be a constructively finite type
variables (X : Type) [fintype X]

example : X = X :=
begin
  -- _inst_1 : fintype X
  unfreezingI {cases _inst_1 }, -- it's a finset under the hood, plus a proof
  -- that everything is in it!
  refl,
end

-- Lean knows that `fin n` is constructively finite
example (n : ℕ) : fintype (fin n) := infer_instance 

open_locale big_operators

-- the advantage of constructive finiteness is that the elements are internally stored
-- as a list, so you can prove this with `refl`
example : ∑ x : fin 10, x = 45 :=
begin
  refl,
end

-- Actually I just tricked you. Can you explain this?
example : ∑ x : fin 10, x = 25 :=
begin
  refl,
end

-- Here's a better proof
example : ∑ x : fin 10, x.val = 45 :=
begin
  refl
end
-- Take a look at the types of the 45 in those proof. Do you know how to? Do you know
-- what's going on? Hint: ℤ/10ℤ.
