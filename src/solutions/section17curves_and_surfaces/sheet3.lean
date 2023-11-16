/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import data.real.basic
import analysis.calculus.parametric_integral
import analysis.calculus.cont_diff
import analysis.special_functions.trigonometric.deriv

/-

# Smooth functions

-/

noncomputable def φ₁ : ℝ → ℝ × ℝ := 
λ x, (real.cos x, real.sin x)

example : cont_diff_on ℝ ⊤ φ₁ (set.Icc 0 1) :=
begin
  apply cont_diff_on.prod,
  { apply cont_diff.cont_diff_on, 
    exact real.cont_diff_cos,
  },
  { apply cont_diff.cont_diff_on, 
    exact real.cont_diff_sin,
  },
end

open real
noncomputable def φ₂ : ℝ → ℝ × ℝ × ℝ :=
λ x, (real.sin x, x^4+37*x^2+1, abs x)

example : cont_diff_on ℝ ⊤ φ₂ (set.Icc 0 1) :=
cont_diff_sin.cont_diff_on.prod $
  (((cont_diff_id.pow 4).add (cont_diff_const.mul (cont_diff_id.pow 2))).add
  cont_diff_const).cont_diff_on.prod $
  cont_diff_on_id.congr (λ x hx, abs_of_nonneg hx.1)

/- Let `a≤b` and `c≤d` be reals. Let φ : [a,b] → [c,d] and ψ : [c,d] → [a,b]
  be inverse bijections, and assume φ is smooth and φ' is nonvanishing
  on [a,b]. Then ψ is smooth and ψ' is nonvanishing on [c,d],
  and ψ'(y)*φ'(ψ(y))=1.
-/
example (φ : ℝ → ℝ) (ψ : ℝ → ℝ) (a b c d : ℝ)
  (hab : a ≤ b) (hcd : c ≤ d) (hφ : ∀ x, x ∈ set.Icc a b → φ x ∈ set.Icc c d)
  (hψ : ∀ y, y ∈ set.Icc c d → ψ y ∈ set.Icc a b)
  (left_inv : ∀ x, x ∈ set.Icc a b → ψ (φ x) = x)
  (right_inv : ∀ y, y ∈ set.Icc c d → φ (ψ y) = y)
  (hφdiff : cont_diff_on ℝ ⊤ φ (set.Icc a b))
  (hφregular : ∀ x, x ∈ set.Icc a b → fderiv ℝ φ x ≠ 0) :
  cont_diff_on ℝ ⊤ ψ (set.Icc c d) ∧
  ∀ y, y ∈ set.Icc c d → ∀ z, fderiv ℝ ψ y (fderiv ℝ φ (ψ(y)) z) = z :=
sorry

/-
Heather Macbeth: @Kevin Buzzard This is a toy case of the inverse function theorem, 
but you might need to glue together several related results. Some starting points: 
docs#cont_diff_at.to_local_inverse, docs#has_strict_fderiv_at.local_inverse_unique

Heather Macbeth: If you want to construct the inverse, and you want to avoid invoking 
the inverse function theorem on Banach spaces, you can also route through order theory 
for a purely one-dimensional construction. Look at the construction of docs#real.arctan 
for a model; it uses docs#strict_mono_on.order_iso
-/