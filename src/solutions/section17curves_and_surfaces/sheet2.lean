/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import data.real.basic
import analysis.calculus.parametric_integral
import analysis.special_functions.exp_deriv

namespace section17sheet2solutions

/-

# Basic calculus

-/

-- Thanks to Moritz Doll on the Zulip for writing this one!
/-- If `f : ℝ → ℝ` is differentiable at `x`, then the obvious induced function `ℝ → ℂ` is
also differentiable at `x`. -/
lemma complex.differentiable_at_coe {f : ℝ → ℝ} {x : ℝ } (hf : differentiable_at ℝ f x) :
  differentiable_at ℝ (λ y, (f y : ℂ)) x :=
begin
  apply complex.of_real_clm.differentiable_at.comp _ hf,
end

-- Here's a harder example
example (a : ℂ) (x : ℝ) : differentiable_at ℝ (λ (y : ℝ), complex.exp (-(a * ↑y ^ 2))) x :=
begin
  apply differentiable_at.comp,
  { apply differentiable_at.cexp,
    apply differentiable_at_id', },
  { apply differentiable_at.neg,
    apply differentiable_at.mul,
    { apply differentiable_at_const, },
    { norm_cast,
      apply complex.differentiable_at_coe,
      apply differentiable_at.pow,
      apply differentiable_at_id', } },
end

noncomputable def φ₁ : ℝ → ℝ × ℝ := 
λ x, (real.cos x, real.sin x)

example : cont_diff_on ℝ ⊤ (λ x, (real.cos x, real.sin x)) (set.Icc 0 1) :=
begin
  sorry,
end

end section17sheet2solutions