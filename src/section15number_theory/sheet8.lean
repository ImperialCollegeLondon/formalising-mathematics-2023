/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import data.zmod.algebra
import number_theory.wilson

open_locale big_operators

/-

## -1 is a square mod p if p=1 mod 4

I formalise the following constructive proof in the solutions: ((p-1)/2)! works!

-/

lemma exists_sqrt_neg_one_of_one_mod_four (p : ℕ) (hp : p.prime) 
  (hp2 : ∃ n, p = 4 * n + 1) : ∃ i : zmod p, i^2 = -1 :=
begin
  sorry,
end
