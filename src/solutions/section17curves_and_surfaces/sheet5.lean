/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import measure_theory.function.lp_space -- theory of ℓᵖ spaces

/-

# Lᵖ spaces

The set-up : `X` is a type equipped with a (sigma algebra and a) measure.

The space ℒp X
-/

open measure_theory

variables (X : Type) [measurable_space X] (μ : measure X)

-- Instead of functions from X to ℝ, Lean is happy to work with functions from X to
-- some arbitrary `normed_add_comm_group`

variables (F : Type) [normed_add_comm_group F]

-- Functions from X to F have an Lᵖ seminorm defined on them, if `p : ℝ≥0∞`

open_locale ennreal

variables (f : X → F) (p : ℝ≥0∞)

-- the integral (∫ ‖f a‖^p ∂μ) ^ (1/p)
noncomputable example : ℝ≥0∞ := snorm f p μ   

-- `mem_ℒp` is the predicate saying that this integral is finite
example : Prop := mem_ℒp f p μ  

-- The reason it's called `snorm` not `norm`, is because we didn't yet quotient out by 
-- the things whose integral is zero. This quotient is called `Lp`

example : Type := Lp F p μ

example : add_comm_group (Lp F p μ) := 
begin
  apply_instance -- sum of two p-integrable functions is p-integrable
end

-- If 1 ≤ p then it's a normed group
noncomputable example [fact (1 ≤ p)]: normed_add_comm_group (Lp F p μ) := 
begin
  apply_instance
end
