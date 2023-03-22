/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import field_theory.separable
import ring_theory.trace
import ring_theory.norm

/-

# Separable extensions

With infinite fields of characteristic `p`, weird things can happen with extensions, where
an irreducible polynomial can pick up repeated roots in an extension. A separable extension
is an extension where this pathology isn't occurring. Note that in examples like extensions
of number fields, this never happens, because number fields are characteristic zero.


-/

-- Let E ⊆ F be a field extension
variables (E F : Type) [field E] [field F] [algebra E F]

section separable_assumption

-- Here's how you say it's separable
variable [is_separable E F]

-- Separable extensions are algebraic by definition in Lean
example (f : F) : is_algebraic E f :=
begin
  apply is_integral.is_algebraic, -- suffices to prove f is integral over E
  apply is_separable.is_integral, -- follows from separability
end

end separable_assumption

-- finite-dimensional char 0 extensions are separable
example [finite_dimensional E F] [char_zero E] :
  is_separable E F := infer_instance -- typeclass inference can solve this as everything's a typeclass!

-- In the separable case, the minimum polynomial of `f : F` is guaranteed to have distinct roots in
-- a splitting field, and we can define traces and norms as sums or products of conjugates.
-- Let `Ω` be an algebraically closed extension of `E` (note: `Ω` doesn't have to contain `F`)

variables (Ω : Type) [field Ω] [algebra E Ω] [is_alg_closed Ω]

open_locale big_operators

example [is_separable E F] [finite_dimensional E F] (f : F) : 
  algebra_map E Ω (algebra.norm E f) = ∏ σ : F →ₐ[E] Ω, σ f := 
algebra.norm_eq_prod_embeddings E Ω

example [is_separable E F] [finite_dimensional E F] (f : F) :
  algebra_map E Ω (algebra.trace E F f) = ∑ σ : F →ₐ[E] Ω, σ f := 
trace_eq_sum_embeddings Ω

-- Note the inconsistencies in both `algebra.trace/norm` inputs 
-- and `trace/norm_eq_sum/prod_embeddings` inputs. 

-- Now say we have a tower E ⊆ F ⊆ K
variables (K : Type) [field K] [algebra E K] [algebra F K] [is_scalar_tower E F K]

-- If the big extension is separable then so are the two smaller ones
example [is_separable E K] : is_separable E F := is_separable_tower_bot_of_is_separable E F K
example [is_separable E K] : is_separable F K := is_separable_tower_top_of_is_separable E F K

-- I can't find the claim that if F/E and K/F are separable then so is K/E. The proof I know
-- uses separable degree and I'm not sure we have that in Lean either.

