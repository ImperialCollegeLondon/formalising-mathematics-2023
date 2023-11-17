/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet3 -- import the definition of `tends_to` from a previous sheet

namespace section2sheet5

open section2sheet3solutions

-- you can maybe do this one now
theorem tends_to_neg {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n, - a n) (-t) :=
begin
  sorry,
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
  sorry
end

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tends_to_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tends_to a t) (hb : tends_to b u) :
  tends_to (λ n, a n - b n) (t - u) :=
begin
  -- this one follows without too much trouble from earlier results.
  sorry
end

end section2sheet5