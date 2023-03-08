/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import data.zmod.algebra
import number_theory.wilson

open_locale big_operators

lemma factorial_eq_prod (n : ℕ) : n.factorial = ∏ i in finset.Icc 1 n, i :=
begin
  induction n with d hd,
  { refl, },
  { rw [nat.factorial_succ, hd],
    rw finset.Icc_eq_cons_Ico (show 1 ≤ d + 1, by linarith),
    rw finset.prod_cons,
    congr', },
end

lemma wilson_theorem {p n : ℕ}
  (hp : nat.prime p)
  (hn : p = 4 * n + 1) :
     ∏ (j : ℕ) in finset.Icc 1 (4 * n), (j : zmod p) = -1 :=
begin
  have := (nat.prime_iff_fac_equiv_neg_one (_ : p ≠ 1)).1 hp,
  { rw [← this, hn],
    norm_cast,
    congr',
    simp,
    rw factorial_eq_prod,
  },
  { exact nat.prime.ne_one hp, },
end

lemma exists_sqrt_neg_one_of_one_mod_four (p : ℕ) (hp : p.prime) 
  (hp2 : ∃ n, p = 4 * n + 1) : ∃ i : zmod p, i^2 = -1 :=
begin
  cases hp2 with n hn,
  set i := ∏ j in (finset.Icc 1 (2 * n)), (j : zmod p) with hi,
  have h1 : ∏ j in (finset.Icc 1 (2 * n)), (-1 : zmod p) = 1,
  { rw [finset.prod_const],
    simp only [nat.add_succ_sub_one, add_zero, nat.card_Icc],
    rw [pow_mul, neg_one_pow_two, one_pow], },
  have h2 : ∏ j in (finset.Icc 1 (2 * n)), (-j : zmod p) = i,
  { conv_lhs {
      congr, skip, funext,
      rw neg_eq_neg_one_mul,
    },
    rw [finset.prod_mul_distrib, h1, one_mul], },
  have h3 : ∏ j in (finset.Icc (2 * n + 1) (4 * n)), (j : zmod p) = i,
  { rw ←h2,
    apply finset.prod_bij' (λ j hj, p - j) _ _ (λ j hj, p - j),
    { intros,
      dsimp,
      rw finset.mem_Icc at ha,
      cases ha,
      omega, },
    { intros,
      dsimp,
      rw finset.mem_Icc at ha,
      omega, },
    { intros,
      dsimp,
      rw finset.mem_Icc at ha ⊢,
      omega, },
    { intros,
      dsimp,
      rw finset.mem_Icc at ha ⊢,
      omega, },
    { intros,
      dsimp,
      rw finset.mem_Icc at ha,
      rw eq_neg_iff_add_eq_zero,
      suffices : a + (p - a) = p,
      { norm_cast, 
        simp [this], },
      omega, },
  },
  use i,
  rw pow_two,
  nth_rewrite 0 hi,
  rw ←h3,
  rw ← finset.prod_union, 
  { convert_to ∏ j in finset.Icc 1 (4 * n), (j : zmod p) = -1,
    { congr',
      ext,
      rw finset.mem_union,
      simp only [finset.mem_Icc],
      omega, },
    { apply wilson_theorem hp hn, }, },
  { rw disjoint_iff_inf_le,
    rintro x (hx : x ∈ _ ∩ _),
    rw [finset.mem_inter, finset.mem_Icc, finset.mem_Icc] at hx,
    rcases hx with ⟨⟨_, _⟩, _, _⟩,
    linarith,
  },
end
