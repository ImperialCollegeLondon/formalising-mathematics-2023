/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet5 -- import a bunch of previous stuff

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
  intros ε hε,
  obtain ⟨X, hX⟩ := h (ε/37) (by linarith),
  use X,
  intros n hn,
  specialize hX n hn,
  simp,
  rw [← mul_sub, abs_mul, abs_of_nonneg];
  linarith,
end

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tends_to_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tends_to a t)
  {c : ℝ} (hc : 0 < c) : tends_to (λ n, c * a n) (c * t) :=
begin
  intros ε hε,
  obtain ⟨X, hX⟩ := h (ε/c) (div_pos hε hc),
  use X,
  intros n hn,
  specialize hX n hn,
  simp,
  rw [← mul_sub, abs_mul, abs_of_pos hc],
  exact (lt_div_iff' hc).mp hX,
end

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tends_to_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tends_to a t)
  {c : ℝ} (hc : c < 0) : tends_to (λ n, c * a n) (c * t) :=
begin
  have hc' : 0 < -c := neg_pos.mpr hc,
  intros ε hε,
  obtain ⟨X, hX⟩ := h (ε/(-c)) (div_pos hε hc'),
  use X,
  intros n hn,
  specialize hX n hn,
  simp,
  rw [← mul_sub, abs_mul, abs_of_neg hc],
  exact (lt_div_iff' hc').mp hX,
end

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tends_to_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tends_to a t) :
  tends_to (λ n, c * a n) (c * t) :=
begin
  obtain (hc | rfl | hc) := lt_trichotomy 0 c,
  { exact tends_to_pos_const_mul h hc },
  { simpa using tends_to_const 0 },
  { exact tends_to_neg_const_mul h hc }
end

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tends_to_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tends_to a t) :
  tends_to (λ n, a n * c) (t * c) :=
by simpa [mul_comm] using tends_to_const_mul c h

-- another proof of this result, showcasing some tactics
-- which I've not covered yet.
theorem tends_to_neg' {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n, - a n) (-t) :=
begin
  simpa using tends_to_const_mul (-1) ha,
end

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tends_to_of_tends_to_sub {a b : ℕ → ℝ} {t u : ℝ}
  (h1 : tends_to (λ n, a n - b n) t) (h2 : tends_to b u) :
  tends_to a (t+u) :=
begin
  simpa using tends_to_add h1 h2,
end

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tends_to_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} :
  tends_to a t ↔ tends_to (λ n, a n - t) 0 :=
begin
  split,
  { intro h,
    simpa using tends_to_sub h (tends_to_const t) },
  { intro h,
    simpa using tends_to_add h (tends_to_const t) },
end

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tends_to_zero_mul_tends_to_zero
  {a b : ℕ → ℝ} (ha : tends_to a 0) (hb : tends_to b 0) :
  tends_to (λ n, a n * b n) 0 :=
begin
  intros ε hε,
  obtain ⟨X, hX⟩ := ha ε hε, 
  obtain ⟨Y, hY⟩ := hb 1 zero_lt_one,
  use max X Y,
  intros n hn,
  specialize hX n (le_of_max_le_left hn),
  specialize hY n (le_of_max_le_right hn),
  simpa [abs_mul] using mul_lt_mul'' hX hY _ _;
  exact abs_nonneg _,
end

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tends_to_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : tends_to a t)
  (hb : tends_to b u) : tends_to (λ n, a n * b n) (t * u) :=
begin
  -- suffices a(n)b(n)-tu -> 0
  rw tends_to_sub_lim_iff at *,
  -- rewrite as (a(n)-t)*(b(n)-u)+t(b(n)-u)+(a(n)-t)u ->0
  have h : ∀ n, a n * b n - t * u = 
    (a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u,
  { intro n, ring },
  simp [h],
  rw (show (0 : ℝ) = 0 + (t * 0) + (0 * u), by simp),
  refine tends_to_add (tends_to_add _ _) _,
  { exact tends_to_zero_mul_tends_to_zero ha hb },
  { exact tends_to_const_mul t hb },
  { exact tends_to_mul_const u ha },
end

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tends_to_unique (a : ℕ → ℝ) (s t : ℝ)
  (hs : tends_to a s) (ht : tends_to a t) : s = t :=
begin
  by_contra h,
  wlog h2 : s < t,
  { exact ne.lt_or_lt h },
  set ε := t - s with hε,
  have hε : 0 < ε := sub_pos.mpr h2,
  obtain ⟨X, hX⟩ := hs (ε/2) (by linarith),
  obtain ⟨Y, hY⟩ := ht (ε/2) (by linarith),
  specialize hX (max X Y) (le_max_left X Y),
  specialize hY (max X Y) (le_max_right X Y),
  rw abs_lt at hX hY,
  linarith,
end

-- bonus solution: another proof of tends_to_unique inspired
-- by a comment on YT!

-- If |r|<ε for all ε>0 then r=0
lemma eq_zero_of_abs_lt_eps {r : ℝ} (h : ∀ ε > 0, |r| < ε) : r = 0 :=
begin
  -- Proof by contradiction. Say r ≠ 0.
  by_contra h2,
  -- Then let ε be |r|, and we must have ε > 0. 
  specialize h (|r|) (abs_pos.mpr h2),
  -- Deduce |r|<|r|, a contradiction.
  linarith,
end

-- Second proof
theorem tends_to_unique' (a : ℕ → ℝ) (s t : ℝ)
  (hs : tends_to a s) (ht : tends_to a t) : s = t :=
begin
  -- We know a - a tends to s - t because of `tends_to_sub`
  have h := tends_to_sub hs ht,
  -- We want to prove s = t; by previous result suffices to
  -- show |t - s|<ε for all ε>0
  suffices : ∀ ε > 0, |t - s| < ε,
  { linarith [eq_zero_of_abs_lt_eps this] },
  -- Let ε be positive.
  intros ε hε,
  -- There exists X such that for n>=X, |a(n) - a(n) - (s - t)| < ε
  obtain ⟨X, hX⟩ := h ε hε,
  specialize hX X (by refl),
  -- and the simplifier can now reduce that to the goal |t-s|<ε.
  simpa using hX,
end