/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import analysis.calculus.parametric_integral

/-

# Basic calculus

Let's figure out how to do differentiability in Lean together (because as I'm writing this
I have very little clue :-/

section differentiability_in_general

-- OK so this seems to be how to say a function is differentiable:

-- these variables will only live in this section
-- Let 𝕜 be a field equipped with a non-trivial norm (e.g. ℝ)
variables (𝕜 : Type) [nontrivially_normed_field 𝕜] 

-- Let `E` be a 𝕜-vector space with a norm (e.g. ℝ or ℝ²)
variables (E : Type) [normed_add_comm_group E] [normed_space 𝕜 E]

-- and let `F` be another one
variables (F : Type) [normed_add_comm_group F] [normed_space 𝕜 F]

-- Then it makes sense to say that a function `f : E → F` is differentiable
variable (f : E → F)

-- This is the true-false statement that `f` is differentiable.
example : Prop := differentiable 𝕜 f

-- You can also ask that `f` is differentiable at `e : E`

example (e : E) : Prop := differentiable_at 𝕜 f e

-- Here's how you say "`f` is continuously differentiable 37 times"
-- (i.e. you can differentiate f 37 times and when you're done the answer is continuous
-- but might not be differentiable)

example : Prop := cont_diff 𝕜 37 f

-- Here's how you say "`f` is smooth, i.e. infinitely differentiable"

example : Prop := cont_diff 𝕜 ⊤ f

-- That's `⊤` as in "the top element of a lattice" as in `+∞`, not `T` as in "the letter T".
-- Indeed, `cont_diff 𝕜` takes an element of `ℕ∞`.

end differentiability_in_general

-- Let's now just assume `𝕜 = ℝ`; then `E` and `F` can be `ℝ` or `ℂ` or `ℝ × ℝ` or `fin n → ℝ` (the
-- way we say `ℝⁿ` in mathlib) or ...

open real -- because there is `real.cos` and `complex.cos`, 

-- This says "the cos(sin(x))*exp(x) is differentiable"
-- Hint: the theorems are called theorems like `differentiable.mul` etc.
-- Try proving it by hand.

example : differentiable ℝ (λ x, cos (sin x) * exp x) :=
begin
  sorry,
end

-- Now see what `hint` has to say!
example : differentiable ℝ (λ x, cos (sin x) * exp x) :=
begin
  sorry,
end

-- The simplifier can even do this sort of thing:
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }

-- Try this one:
example (a : ℝ) (x : ℝ) : differentiable_at ℝ (λ (y : ℝ), exp (-(a * y ^ 2))) x :=
begin
  sorry,
end

