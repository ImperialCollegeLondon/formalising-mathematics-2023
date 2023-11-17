/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet3 -- import the definition of `tends_to` from a previous sheet

namespace section2sheet5solutions

open section2sheet3solutions

-- you can maybe do this one now
theorem tends_to_neg {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n, - a n) (-t) :=
begin
  rw tends_to_def at *,
  have h : ∀ n, |a n - t| = | -a n - -t|,
  { intro n,
    rw abs_sub_comm,
    congr' 1,
    ring },
  simpa [h] using ha,
end

/-
`tends_to_add` is quite a challenge. In a few weeks' time I'll
show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful. 
-/

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tends_to_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n + b n) (t + u) :=
begin
  rw tends_to_def at *,
  -- let ε > 0 be arbitrary
  intros ε hε,
  --  There's a bound X such that if n≥X then a(n) is within ε/2 of t
  specialize ha (ε/2) (by linarith),
  cases ha with X hX,
  --  There's a bound Y such that if n≥Y then b(n) is within ε/2 of u
  obtain ⟨Y, hY⟩ := hb (ε/2) (by linarith),
  --  use max(X,Y),
  use max X Y,
  -- now say n ≥ max(X,Y)
  intros n hn,
  rw max_le_iff at hn,
  specialize hX n hn.1,
  specialize hY n hn.2,
  --  Then easy.
  rw abs_lt at *,
  split; -- semicolon means "do next tactic to all goals produced by this tactic"
  linarith,
end

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tends_to_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n - b n) (t - u) :=
begin
  simpa [sub_eq_add_neg] using tends_to_add ha (tends_to_neg hb),
end

end section2sheet5solutions

