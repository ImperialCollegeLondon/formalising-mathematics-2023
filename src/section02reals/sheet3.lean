/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers

/-

# Limits of sequences in Lean

We give the standard `ε`, `N` definition of the limit of a sequence
and prove some theorems about them.

## lambda (λ) notation for functions

Here's how we define the functions from the naturals to the reals
sending n to n^2 + 3:

-/

def f : ℕ → ℝ := λ n, n^2 + 3

/-

Mathematicians might write `n ↦ n^2+3` for this functions; indeed `λ` is
just prefix notation for the infix notation `↦` (i.e. you write `λ` at
the front and `↦` in the middle but they mean the same thing). You can
read more about function types in the "three kinds of types" section
of Part B of the course book.

Sometimes you might find yourself with a lambda-defined function
evaluated at a number. For example, you might see something like
`(λ n, n^2 + 3) 37`, which means "take the function sending
`n` to `n^2+3` and then evaluate it at 37". You can use the `dsimp`
(or `dsimp only`) tactic to simplify this to `37^2+3`.

The reason we need to know about function notation for this sheet
is that a sequence `x₀, x₁, x₂, …` of reals on this sheet will
be encoded as a function from `ℕ` to `ℝ` sending `0` to `x₀`, `1` to `x₁`
and so on.
 
## Limit of a sequence.

Here's the definition of the limit of a sequence.
-/

/-- If `a(n)` is a sequence of reals and `t` is a real, `tends_to a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def tends_to (a : ℕ → ℝ) (t : ℝ) : Prop :=
∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/-

We've made a definition, so it's our job to now make the API
for the definition, i.e. prove some basic theorems about it. 
-/

-- If your goal is `tends_to a t` and you want to replace it with
-- `∀ ε > 0, ∃ B, …` then you can do this with `rw tends_to_def`.
theorem tends_to_def {a : ℕ → ℝ} {t : ℝ} :
  tends_to a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
begin
  -- true by definition
  refl
end

-- the eagle-eyed viewers amongst you might have spotted
-- that `∀ ε > 0, ...` and `∀ ε, ε > 0 → ...` and `∀ ε, 0 < ε → ...`
-- are all definitionally equal, so `refl` sees through them. 

/-

## The questions

Here are some basic results about limits of sequences.
See if you can fill in the `sorry`s with Lean proofs.
Note that `norm_num` can work with `|x|` if `x` is a numeral like 37,
but it can't do anything with it if it's a variable.
-/

/-- The limit of the constant sequence with value 37 is 37. -/
theorem tends_to_thirtyseven : tends_to (λ n, 37) 37 :=
begin
  sorry,
end

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tends_to_const (c : ℝ) : tends_to (λ n, c) c :=
begin
  sorry,
end

/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
theorem tends_to_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ)
  (h : tends_to a t) :
  tends_to (λ n, a n + c) (t + c) :=
begin
  sorry,
  -- hints: make sure you know the maths proof!
  -- use `cases` to deconstruct an `exists`
  -- hypothesis, and `specialize` to specialize
  -- a `forall` hypothesis to specific values.
  -- Look up the explanations of these tactics in Part C
  -- of the course notes. 
end

-- you're not quite ready for this one yet though.
/-- If `a(n)` tends to `t` then `-a(n)` tends to `-t`.  -/
example {a : ℕ → ℝ} {t : ℝ} (ha : tends_to a t) :
  tends_to (λ n, - a n) (-t) :=
begin
  sorry,
  -- Try this one. You don't know enough material to do it yet!
  -- Where do you get stuck? The problem is that I didn't teach you
  -- any "API" for (a.k.a. theorems about) the absolute value function |.|.
  -- We need to figure out how to prove |(-x)| = |x|,
  -- or |a - b| = |b - a| or something like that.
  -- Leave this for now and try sheet 4, where you'll learn how to discover these things.
  -- We'll come back to this example on sheet 5. 
end
