/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import measure_theory.measurable_space

/-

# Measure theory

A σ-algebra on a type `X` is a collection of subsets of `X` satisfying some
axioms, and in Lean you write it like this:

-/

section examples

-- let X be a set
variable (X : Type)
-- ...and let 𝓐 be a sigma-algebra on X
variable (𝓐 : measurable_space X)

/-
Usually `X` will only have one measurable space structure on it, so we can
use the typeclass system. But right now let's mess around with several
measurable space structures on `X`.

If `A` is a subset of `X` then {0,A,Aᶜ,X} is a sigma algebra.

-/

def gen_by (A : set X) : measurable_space X :=
{ measurable_set' := λ S, S = ∅ ∨ S = A ∨ S = Aᶜ ∨ S = ⊤,
  measurable_set_empty := begin
    left, refl,    
  end,
  measurable_set_compl := begin
    rintro s (h | h | h | h),
    { right, right, right, simp [h], },
    { right, right, left, rw [h], },
    { right, left, rw h, simp, },
    { left, rw h, simp, },
  end,
  measurable_set_Union := begin
    intros f hf,
    by_cases h1 : ∃ j, f j = ⊤,
    { right, right, right,
      rw eq_top_iff,
      rintro x -,
      rw set.mem_Union,
      cases h1 with j hj,
      use j,
      rw hj,
      triv, },
    push_neg at h1,
    by_cases h2 : ∃ j k, f j = A ∧ f k = Aᶜ,
    { right, right, right, rw eq_top_iff, rintro x -,
    rw set.mem_Union,
    rcases h2 with ⟨j, k, hj, hk⟩,
    by_cases hxA : x ∈ A,
    { use j,
      rwa hj, },
    { use k,
      rwa hk, }, }, 
    push_neg at h2,
    by_cases h3 : ∃ j, f j = A,
    { right, left,
      ext x,
      rw set.mem_Union,
      cases h3 with j hj,
      split,
      { rintro ⟨i, hi⟩,
        suffices : f i ⊆ A,
        { exact this hi, },
        rcases hf i with (h|h|h|h),
        { rw h, simp, },
        { rw h, },
        { cases h2 j i hj h, },
        { cases h1 i h, }, }, 
      { intro hx,
        use j,
        rwa hj, }, }, 
    by_cases h4 : ∃ j, f j = Aᶜ,
    { right, right, left,
      ext x,
      rw set.mem_Union,
      cases h4 with j hj,
      split,
      { rintro ⟨i, hi⟩,
        suffices : f i ⊆ Aᶜ,
        { exact this hi, },
        rcases hf i with (h|h|h|h),
        { rw h, simp, },
        { cases h2 i j h hj, },
        { rw h, simp, },
        { cases h1 i h, }, }, 
      { intro hx,
        use j,
        rwa hj, }, }, 
    push_neg at h3 h4,
    left,
    apply set.eq_empty_of_subset_empty,
    intros x hx,
    rw set.mem_Union at hx,
    cases hx with i hi,
    rcases hf i with (h|h|h|h),
    { rwa h at hi, },
    { cases h3 _ h, },
    { cases h4 _ h, },
    { cases h1 _ h, },      
  end }

example (A : set X) : measurable_space X := measurable_space.generate_from {A}

example (A : set X) : (measurable_space.generate_from {A}).measurable_set' = ({∅,A,Aᶜ,⊤} : set (set X)) := 
begin
  ext B,
  simp,
  unfold measurable_space.generate_from,
  dsimp,
  split,
  { intro h,
    induction h with A' hA' C hC1 hC2 f hf1 hf2,
    { simp at hA', right, left, assumption, },
    { left, refl, },
    { rcases hC2 with (rfl|rfl|rfl|rfl);
      finish, },
    { dsimp at hf2,
      exact (gen_by X A).measurable_set_Union f hf2, }, },
  { rintro (rfl|rfl|rfl|rfl),
    { apply measurable_space.generate_measurable.empty, },
    { apply measurable_space.generate_measurable.basic, simp, },
    { apply measurable_space.generate_measurable.compl, apply measurable_space.generate_measurable.basic, simp, },
    { rw (show (set.univ : set X) = ∅ᶜ,by simp), 
      apply measurable_space.generate_measurable.compl, apply measurable_space.generate_measurable.empty, }, },
end


end examples
