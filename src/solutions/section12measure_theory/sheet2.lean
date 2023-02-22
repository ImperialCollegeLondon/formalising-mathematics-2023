/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import measure_theory.measurable_space

/-

# Measure theory

## More on sigma algebras.

-/

-- Intersection of sigma algebras is a sigma algebra

-- Let 𝓐 be a family of sigma algebras on a type `X`
variables (X : Type) (I : Type) (𝓐 : I → measurable_space X)

-- Then their intersection is also a sigma algebra

open_locale measure_theory -- to get notation `measurable_set[S] U` for "U is in the sigma algebra S"
example : measurable_space X :=
{ measurable_set' := λ U, ∀ i : I, measurable_set[𝓐 i] U,
  measurable_set_empty := begin
    intro i,
    apply measurable_set.empty,
  end,
  measurable_set_compl := begin
    intros s hs i,
    apply measurable_set.compl,
    apply hs,
  end,
  measurable_set_Union := begin
    intros f h i,
    apply measurable_set.Union,
    intro j,
    apply h,
  end }

-- Lean knows that sigma algebras on X are a complete lattice
-- so you could also make it like this:
example : measurable_space X := ⨅ i, 𝓐 i

-- Sigma algebras are closed under countable intersection
-- Here, because there's only one sigma algebra involved,
-- I use the typeclass inference system to say "fix a canonical
-- sigma algebra on X" and just use that one throughout the question.
example (X : Type) [measurable_space X] (f : ℕ → set X)
  (hf : ∀ n, measurable_set (f n)) : measurable_set (⋂ n, f n) :=
begin
  rw ← measurable_set.compl_iff,
  rw set.compl_Inter,
  apply measurable_set.Union,
  intro b,
  apply measurable_set.compl,
  apply hf,
end

