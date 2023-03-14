/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import analysis.normed_space.lp_space -- theory of ℓᵖ spaces

/-

# ℓᵖ spaces

The set-up : `I` is an index type, `E` is a family of `normed_add_comm_group`s
(so if `i : I` then `E i` is a type and if `v : E i` then `‖v‖` makes sense and
is a real number).

Then given `p : ℝ≥0∞` (i.e. an element `p` of `[0,∞]`) there is a theory
of ℓᵖ spaces, which is the subspace of `Π i, E i` (the product) consisting of the
sections `vᵢ` such that `∑ᵢ ‖vᵢ‖ᵖ < ∞`. For `p=∞` this means "the ‖vᵢ‖ are
bounded".

-/

open_locale ennreal -- to get notation ℝ≥0∞

variables (I : Type) (E : I → Type) [∀ i, normed_add_comm_group (E i)] (p : ℝ≥0∞)

-- Here's how to say that an element of the product of the Eᵢ is in the ℓᵖ space

example (v : Π i, E i) : Prop := mem_ℓp v p

-- Technical note: 0^0=1 and x^0=0 for x>0, so ℓ⁰ is the functions with finite support.

variable (v : Π i, E i)

example : mem_ℓp v 0 ↔ set.finite {i | v i ≠ 0} :=
begin
  exact mem_ℓp_zero_iff,
end

example : mem_ℓp v ∞ ↔ bdd_above (set.range (λ i, ‖v i‖)) :=
begin
  exact mem_ℓp_infty_iff,
end

-- The function ennreal.to_real sends x<∞ to x and ∞ to 0. 
-- So `0 < p.to_real` is a way of saying `0 < p < ∞`. 

example (hp : 0 < p.to_real) : 
  mem_ℓp v p ↔ summable (λ i, ‖v i‖ ^ p.to_real) :=
begin
  exact mem_ℓp_gen_iff hp
end

-- It's a theorem in the library that if p ≤ q then mem_ℓp v p → mem_ℓp v q

example (q : ℝ≥0∞) (hpq : p ≤ q) : mem_ℓp v p → mem_ℓp v q := 
begin
  intro h,
  exact h.of_exponent_ge hpq,
end


-- The space of all `v` satisfying `mem_ℓp v p` is
-- called lp E p

example : Type := lp E p 

-- It has a norm:

noncomputable example (v : lp E p) : ℝ := ‖v‖  

-- It's a `normed_add_comm_group` if `1 ≤ p` but I've not stated this correctly.

noncomputable example (h : 1 ≤ p) : normed_add_comm_group (lp E p) :=
begin
  sorry,
end


-- `real.is_conjugate_exponent p q` means that `p,q>1` are reals and `1/p+1/q=1`

example (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) : 
  p.is_conjugate_exponent q :=
sorry -- it's a structure

-- We have a verison of Hoelder's inequality.

example (q : ℝ≥0∞) (hpq : p.to_real.is_conjugate_exponent q.to_real) (f : lp E p)
  (g : lp E q) : ∑' (i : I), ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ :=
begin
  have := lp.tsum_mul_le_mul_norm hpq f g,
  exact this.2,
end

-- This would be a useless theorem if `∑' (i : I), ‖f i‖ * ‖g i‖` diverged,
-- because in Lean if a sum diverges then by definition the `∑'` of it is 0. 
-- So we also need this:

example (q : ℝ≥0∞) (hpq : p.to_real.is_conjugate_exponent q.to_real) (f : lp E p)
  (g : lp E q) : summable (λ i, ‖f i‖ * ‖g i‖) :=
begin
  have := lp.tsum_mul_le_mul_norm hpq f g,
  exact this.1,
end
