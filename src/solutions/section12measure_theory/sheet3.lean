/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import measure_theory.measurable_space

/-

# The extended nonnegative reals [0,∞]

The big dilemma when a designer is faced with "minor modifications"
of a standard type, is whether to just stick with the standard type
and make do, or whether to make a new type and then be faced with the
problem of having to make all the API for that type. Example: in measure
theory a key role is played by the "extended non-negative reals",
namely {x : ℝ | 0 ≤ x} ∪ {∞}. In Lean these are their own type,
called `ennreal`. There is a "locale" containing standard notation
associated for this type. Let's open it.


localized "notation (name := ennreal) `ℝ≥0∞` := ennreal" in ennreal
localized "notation (name := ennreal.top) `∞` := (⊤ : ennreal)" in ennreal
-/

open_locale ennreal

#print notation ℝ≥0∞
#check ennreal


#check ℝ≥0∞ -- [0,∞]

#check ∞ -- it's the ∞ in ℝ≥0∞

-- What can we do with extended non-negative reals?

variables (a b : ℝ≥0∞)

#check a + b
#check a - b -- surprising?
#check a * b -- what is 0 * ∞ then?
#check a / b -- is 1 / 0 = 0 or ∞? In ℝ it's 0 but here there's another possibility

example : (0 : ℝ≥0∞) * ∞ = 0 :=
begin
  norm_num,
end

example : (1 : ℝ≥0∞) / 0 = ∞ :=
begin
  simp,
end

example (a b c : ℝ≥0∞) : (a + b) * c = a * c + b * c :=
begin
  ring,
end
