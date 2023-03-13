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

But this time it's nasty.

Let's *start* to prove Theorem 3.6 following Conrad: if R is Noetherian then R[X] is
Noetherian.

It's not impossible, but it's messy, to make a complex recursive
definition in the middle of a proof, so we factor it out and do it first.
The set-up is: R is a commutative ring and I ⊆ R[X] is an ideal which
is *not* finitely-generated. We then define a sequence fₙ of elements of R[X]
by strong recursion: fₙ is an element of smallest degree in `I - (f₀,f₁,…fₙ₋₁)`;
note that such an element must exist as `I` is not finitely-generated (and ℕ is
well-ordered).

-/

open_locale polynomial -- for R[X] notation

-- Here's how Conrad's proof starts 
example (R : Type) [comm_ring R] [is_noetherian_ring R] : 
  is_noetherian_ring R[X] :=
begin
  -- Suffices to prove all ideals are finitely generated
  rw is_noetherian_ring_iff_ideal_fg,
  -- By contradiction. Assume `I` isn't.
  by_contra h, push_neg at h, rcases h with ⟨I, hInotfg⟩,
  -- Define a sequence fₙ of elements of `I` by strong recursion: 
  -- fₙ is an element of smallest degree in I - (f₀,f₁,…,fₙ₋₁)
  sorry, -- we won't fill this in, let's just discuss how to define `fₙ`
  -- (the proof is quite long even after this construction)
end

-- If I is a non-finitely-generated ideal of a commutative ring A,
-- and f₀,f₁,...,fₙ₋₁ are elements of I, then I - (f₀,f₁,…,fₙ₋₁) is nonempty
lemma lemma1 {A : Type} [comm_ring A] [decidable_eq A] (I : ideal A) (hInonfg : ¬ I.fg) (n : ℕ)
  (g : Π m, m < n → I) : 
  set.nonempty ((I : set A) \ (ideal.span (finset.image (λ m : fin n, (g m.1 m.2).1) finset.univ : set A))) :=
begin
  sorry,
end

-- If a subset of a set with a "ℕ-valued height function" (e.g. R[X] with `polynomial.nat_degree)
-- is nonempty, then this is a function which returns an element with smallest height.
def smallest_height {A : Type} (h : A → ℕ) {S : set A} (hs : set.nonempty S) : S :=
sorry

-- The function Conrad wants:
def f {R : Type} [comm_ring R] {I : ideal R[X]} (hInonfg : ¬ I.fg) 
  : ℕ → I := 
sorry
