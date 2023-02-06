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

This is `[fintype X]`. It's (in my opinion) harder to use, but it seems to be
the only one for which finite sums work.

-/

variables (X : Type) [fintype X]

open_locale big_operators

example : ∑ x : fin 10, x = 45 := rfl 

example : ∑ x : fin 10, x.1 = 45 := rfl 

-- Take a look at the types of the 45 in this proof. Do you know how to?
