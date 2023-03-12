/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import ring_theory.noetherian -- theory of Noetherian rings
import ring_theory.polynomial

/-

# Commutative algebra

More Conrad, again from 

https://kconrad.math.uconn.edu/blurbs/ringtheory/noetherian-ring.pdf

Let's prove Theorem 3.6 following Conrad: if R is Noetherian then R[X] is
Noetherian.

It's not impossible, but it's messy, to make a slightly complex recursive
definition in the middle of a proof, so we factor it out and do it first.
The set-up is: R is a commutative ring and I ⊆ R[X] is an ideal which
is *not* finitely-generated. We then define a sequence fₙ of elements of R[X]
by strong recursion: fₙ is an element of smallest degree in `I - (f₀,f₁,…fₙ₋₁)`;
note that such an element must exist as `I` is not finitely-generated (and ℕ is
well-ordered).

-/

open_locale polynomial -- for R[X] notation

-- If I is a non-finitely-generated ideal of a commutative ring A,
-- and f₀,f₁,...,fₙ₋₁ are elements of I, then I - (f₀,f₁,…,fₙ₋₁) is nonempty

lemma lemma1 {A : Type} [comm_ring A] [decidable_eq A] (I : ideal A) (hInonfg : ¬ I.fg) (n : ℕ)
  (f : Π m, m < n → I) : 
  set.nonempty ((I : set A) \ (ideal.span (finset.image (λ m : fin n, (f m.1 m.2).1) finset.univ : set A))) :=
begin
  rw set.nonempty_iff_ne_empty,
  intro h,
  rw set.diff_eq_empty at h,
  apply hInonfg,
  refine ⟨finset.image (λ (m : fin n), (f m.1 m.2).val) finset.univ, _⟩,
  refine le_antisymm _ h,
  rw ideal.span_le,
  intros a ha,
  simp only [fin.val_eq_coe, subtype.val_eq_coe, finset.coe_image, finset.coe_univ, set.image_univ, set.mem_range] at ha,
  rcases ha with ⟨y, rfl⟩,
  exact (f y.1 y.2).2,
end

def f {R : Type} [comm_ring R] {I : ideal R[X]} (hInonfg : ¬ I.fg) : ℕ → I :=
nat.strong_rec' (λ n h, sorry)

example (R : Type) [comm_ring R] [is_noetherian_ring R] : 
  is_noetherian_ring R[X] :=
begin
  -- Suffices to prove all ideals are finitely generated
  rw is_noetherian_ring_iff_ideal_fg,
  -- By contradiction. Assume `I` isn't.
  by_contra h, push_neg at h, rcases h with ⟨I, hInotfg⟩,
  -- Define a sequence fₙ of elements of `I` by strong recursion: 
  -- fₙ is an element of smallest degree in I - (f₀,f₁,…,fₙ₋₁)
  sorry,  
end
