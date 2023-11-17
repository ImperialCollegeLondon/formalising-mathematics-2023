/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet5 -- import a bunch of previous stuff

namespace section2sheet6
open section2sheet3solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in a solutions video,
so if you like you can try some of them and then watch me
solving them.

Good luck! 
-/


/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tends_to_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : tends_to a t) :
  tends_to (λ n, 37 * a n) (37 * t) :=
begin
  sorry,
end

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tends_to_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tends_to a t)
  {c : ℝ} (hc : 0 < c) : tends_to (λ n, c * a n) (c * t) :=
begin
  sorry,
end

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tends_to_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tends_to a t)
  {c : ℝ} (hc : c < 0) : tends_to (λ n, c * a n) (c * t) :=
begin
  sorry,
end

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tends_to_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tends_to a t) :
  tends_to (λ n, c * a n) (c * t) :=
begin
  sorry,
end

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tends_to_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tends_to a t) :
  tends_to (λ n, a n * c) (t * c) :=
begin
  sorry
end

-- another proof of this result, showcasing some tactics
-- which I've not covered yet.
theorem tends_to_neg' {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n, - a n) (-t) :=
begin
  convert tends_to_const_mul (-1) ha, -- read about the `convert` tactic in the course notes!
  { ext, simp }, -- ext is a generic extensionality tactic. Here it's being
                 -- used to deduce that two functions are the same if they take
                 -- the same values everywhere
  { simp },
end

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tends_to_of_tends_to_sub {a b : ℕ → ℝ} {t u : ℝ}
  (h1 : tends_to (λ n, a n - b n) t) (h2 : tends_to b u) :
  tends_to a (t+u) :=
begin
  sorry,
end

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tends_to_sub_lim {a : ℕ → ℝ} {t : ℝ}
  (h : tends_to a t) : tends_to (λ n, a n - t) 0 :=
begin
  sorry,
end

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tends_to_zero_mul_tends_to_zero
  {a b : ℕ → ℝ} (ha : tends_to a 0) (hb : tends_to b 0) :
  tends_to (λ n, a n * b n) 0 :=
begin
  sorry,
end

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tends_to_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : tends_to a t)
  (hb : tends_to b u) : tends_to (λ n, a n * b n) (t * u) :=
begin
  sorry,
end

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tends_to_unique (a : ℕ → ℝ) (s t : ℝ)
  (hs : tends_to a s) (ht : tends_to a t) : s = t :=
begin
  sorry,
end

end section2sheet6