/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import data.real.basic
import analysis.calculus.parametric_integral

/-

# Curves and surfaces

Let's see how feasible this is!

-/

noncomputable def φ₁ : ℝ → ℝ × ℝ := 
λ x, (real.cos x, real.sin x)

example : cont_diff_on ℝ ⊤ (λ x, (real.cos x, real.sin x)) (set.Icc 0 1) :=
begin
  sorry,
end

