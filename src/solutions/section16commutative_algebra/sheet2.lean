/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import ring_theory.noetherian -- theory of Noetherian rings
import ring_theory.polynomial.basic

namespace section16sheet2solutions
/-

# Commutative algebra

More Conrad, again from 

https://kconrad.math.uconn.edu/blurbs/ringtheory/noetherian-ring.pdf

Let's *start* to prove Theorem 3.6 following Conrad: if R is Noetherian then R[X] is
Noetherian.

It's not impossible, but it's also not advisable, to make a complex recursive
definition in the middle of a proof. So we factor it out and do it first.
The set-up is: R is a commutative ring and I ⊆ R[X] is an ideal which
is *not* finitely-generated. We then define a sequence fₙ of elements of R[X]
by strong recursion: fₙ is an element of smallest degree in `I - (f₀,f₁,…fₙ₋₁)`;
note that such an element must exist as `I` is not finitely-generated (and ℕ is
well-ordered).

-/

open_locale polynomial -- for R[X] notation

-- If I is a non-finitely-generated ideal of a commutative ring A,
-- and f₀,f₁,...,fₙ₋₁ are elements of I, then I - (f₀,f₁,…,fₙ₋₁) is nonempty

lemma lemma1 {A : Type} [comm_ring A] [decidable_eq A] {I : ideal A} (hInonfg : ¬ I.fg) (n : ℕ)
  (g : Π m, m < n → I) : 
  set.nonempty ((I : set A) \ (ideal.span (finset.image (λ m : fin n, (g m.1 m.2).1) finset.univ : set A))) :=
begin
  rw set.nonempty_iff_ne_empty,
  intro h,
  rw set.diff_eq_empty at h,
  apply hInonfg,
  refine ⟨finset.image (λ (m : fin n), (g m.1 m.2).val) finset.univ, _⟩,
  refine le_antisymm _ h,
  rw ideal.span_le,
  intros a ha,
  simp only [fin.val_eq_coe, subtype.val_eq_coe, finset.coe_image, finset.coe_univ, set.image_univ, set.mem_range] at ha,
  rcases ha with ⟨y, rfl⟩,
  exact (g y.1 y.2).2,
end

#check function.argmin_on

open_locale classical

-- I still haven't sorted out this definition and right now I need to prepare the curves
-- and surfaces lecture :-/ Anyway, the moral of this sheet is that making complicated
-- definitions is perhaps more annoying than you might think :-/
noncomputable def f {R : Type} [comm_ring R] {I : ideal R[X]} [decidable_eq I] 
  (hInonfg : ¬ I.fg) (n : ℕ) : R[X] := nat.strong_rec_on' n $ 
  λ m hm, function.argmin_on (polynomial.nat_degree : R[X] → ℕ) (is_well_founded.wf) _ $
  lemma1 hInonfg n sorry

#exit  
(λ n h, (⟨((lemma2 (polynomial.nat_degree) (lemma1 I hInonfg n h)).some : R[X]), begin
  have := (lemma2 (polynomial.nat_degree) (lemma1 I hInonfg n h)).some_spec,
  have this2 := set.mem_of_mem_diff this.1,
  exact this2,
end⟩ : I))

lemma hf1 {R : Type} [comm_ring R] {I : ideal R[X]} (hInonfg : ¬ I.fg)  (n : ℕ) : 
  (f hInonfg n).1 ∈ (I : set R[X]) \ (ideal.span (finset.image (λ m : fin n, (f hInonfg m).1) finset.univ : set R[X])) :=
begin
  unfold f,
  rw nat.strong_rec_on_beta',
  dsimp,
  sorry,
end

lemma hf2 {R : Type} [comm_ring R] {I : ideal R[X]} (hInonfg : ¬ I.fg) (n : ℕ)
  (i : R[X]) (hi : i ∈ (I : set R[X]) \ (ideal.span (finset.image (λ m : fin n, (f hInonfg m).1) finset.univ : set R[X]))) : 
  polynomial.nat_degree (f hInonfg n).1 ≤ polynomial.nat_degree i :=
begin
  sorry
end

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

end section16sheet2solutions