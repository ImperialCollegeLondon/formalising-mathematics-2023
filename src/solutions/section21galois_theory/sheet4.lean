/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import field_theory.normal

/-

# Normal extensions

Normal extensions are splitting fields. They play a role in Galois theory
because they correspond to normal subgroups via the fundamental theorem.
In Lean, normal implies algebraic.

Say F/E is an extension of fields

-/

variables (E F : Type) [field E] [field F] [algebra E F]

section is_normal

-- Say furthermore F/E is normal

variable [normal E F]

-- Then F/E is algebraic

example (f : F) : is_algebraic E f := normal.is_algebraic infer_instance f

-- and all min polys split

open polynomial

example (f : F) : splits (algebra_map E F) (minpoly E f) := normal.splits infer_instance f

end is_normal

-- A finite extension is normal iff it's the splitting field of a polynomial

open_locale polynomial
open polynomial

example [finite_dimensional E F] : normal E F ↔ ∃ p : E[X], is_splitting_field E F p :=
⟨λ h, by exactI normal.exists_is_splitting_field E F, λ ⟨p, hp⟩, by exactI normal.of_is_splitting_field p⟩

/- 

Note that in that proof I had to use `by exactI` which jumps into tactic mode, resets the instance
cache (because I've just `intro`ed something which should be in it but isn't), and jumps back
into term mode.

PS the proof of `normal.of_is_splitting_field` is a 60 line monster.

## Normal closures

Say E ⊆ F ⊆ Ω is a tower of field extensions. The normal closure of F/E in Ω is naturally a subfield of
Ω containing `F`, and there's a special structure for this: `intermediate_field F Ω`, which we'll
see in the fundamental theorem. 

-/

noncomputable theory

-- Say E ⊆ F ⊆ Ω
variables (Ω : Type) [field Ω] [algebra E Ω] [algebra F Ω] [is_scalar_tower E F Ω] 

example : intermediate_field F Ω := normal_closure E F Ω

-- Note that `normal_closure E F Ω` is a term (of type `intermediate_field F Ω`) but it has a coercion
-- to a type, and that type has a field structure and is normal over `E` if `Ω/E` is normal

example [normal E Ω] : normal E (normal_closure E F Ω) := normal_closure.normal E F Ω

