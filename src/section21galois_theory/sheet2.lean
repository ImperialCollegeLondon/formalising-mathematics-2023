/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import algebra.algebra.tower
import ring_theory.norm -- for norms
import ring_theory.trace -- for traces

/-

# Extensions of extensions

The problem with making every field a type and using `algebra` to
fix the embeddings from a smaller field to a bigger one, is that
when you have three or more extensions, you need to have a way of
saying that those maps are compatible.

On paper we might write "Let `E ⊆ F ⊆ K` be a tower of fields"
but in Lean we make each each pair into an `algebra` structure
and now we want to somehow explain that the `algebra_map` from
`E` to `F` composed with the one from `F` to `K` equals the
one from `E` to `K`. We assert this compatibility with
the `is_scalar_tower E F K` typeclass. Here's the proof
that in the presence of this prop-valued hypothesis, the
diagram commutes.

-/

example (E F K : Type) [field E] [field F] [field K] [algebra E F] [algebra F K]
  [algebra E K] [is_scalar_tower E F K] (e : E) : 
  algebra_map E K e = algebra_map F K (algebra_map E F e) := is_scalar_tower.algebra_map_apply E F K e

/-

For me, what is surprising is that the definition of `is_scalar_tower` is
not at all what one would expect. The idea is due to Kenny Lau (a former Imperial
undergraduate) in 2020; Eric Wieser wrote a paper on how the system works in 2021
https://arxiv.org/abs/2108.10700  (this is Eric on the Discord). Guess what the
definition is and then right click on `is_scalar_tower` and jump to definition
to find out the truth (which might surprise you).

Now we have three compatible field extensions we can ask how the basic constructions
such as degree, norm and trace behave.

-/

variables (E F K : Type) [field E] [field F] [field K] [algebra E F] [algebra F K]
  [algebra E K] [is_scalar_tower E F K] 

-- There is a mathematically correct tower law, involving cardinals:
example : module.rank E F * module.rank F K = module.rank E K := dim_mul_dim E F K

-- But this is a pain to use, because cardinals are not a particularly well-behaved
-- object. So let's put in a finite-dimensional hypothesis and use `finrank`.

open finite_dimensional

-- Tower law for dimensions, natural number case.
example [finite_dimensional E F] : finrank E F * finrank F K = finrank E K := finrank_mul_finrank E F K

/- Note that if K/F is infinite-dimensional then `finrank F K = 0` as does `finrank E K`.
The same argument should apply if F/E is infinite-dimensional; this seems to be a minor
glitch in mathlib!
-/

-- Tricky exercise: look at proof of `finrank_mul_finrank` in mathlib and see if you
-- can generalise it by removing the `[finite_dimensional E F]` condition in the case
-- where everything is a field.
example : finrank E F * finrank F K = finrank E K :=
begin
  sorry,
end

-- trace of trace is trace in a tower
example [finite_dimensional E F] [finite_dimensional F K] (k : K) : 
  (algebra.trace E F) ((algebra.trace F K) k) = (algebra.trace E K) k := algebra.trace_trace k

-- I can't find the norm version though :-/ 
