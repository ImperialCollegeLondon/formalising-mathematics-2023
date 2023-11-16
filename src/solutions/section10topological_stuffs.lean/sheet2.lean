/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/
import tactic

import topology.subset_properties
import ring_theory.int.basic

/-!
# Proof of infinitude of prime numbers using topology

This file contains an interesting proof of infinitude of prime numbers.

Define a topology on `ℤ` by declaring a set `U` is open if and only if 
for every `x ∈ U`, there exists an `1 ≤ m` such that `mk + x ∈ U` for all `k`. 

Then one can see that every nonempty open set is infinite and every arithmetic
progression `{mk + a | k ∈ ℤ}` is both open and closed where `1 ≤ m`.

Then suppose there are only finitely many prime numbers, then `⋃_p {pk | k ∈ ℤ}`
is a finite union of arithmetic progression thus closed, so its complement is open.
However, the complement of `⋃_p {pk | k ∈ ℤ}` is precisely `{-1, 1}` which cannot
be open because it is nonempty but finite.
-/

open topological_space

def contains_arith_progression (U : set ℤ) : Prop :=
∀ (x : ℤ), x ∈ U → ∃ (m : ℤ), 1 ≤ m ∧ ∀ (k : ℤ), m * k + x ∈ U

lemma univ_contains_arith_progression : contains_arith_progression set.univ :=
λ x _, ⟨1, le_refl _, λ _, ⟨⟩⟩

lemma inter_contains_arith_progression (s t : set ℤ) 
  (hs : contains_arith_progression s) (ht : contains_arith_progression t) :
  contains_arith_progression (s ∩ t) :=
begin 
  choose fs hfs1 hfs2 using hs,
  choose ft hft1 hft2 using ht,
  rintros x ⟨hx1, hx2⟩,
  refine ⟨fs _ hx1 * ft _ hx2, _, λ k, ⟨_, _⟩⟩,
  { specialize hfs1 x hx1, 
    specialize hft1 x hx2,
    have ineq := mul_le_mul hfs1 hft1 _ _,
    { rwa one_mul at ineq,  },
    all_goals { linarith }, },
  { rw [mul_assoc], apply hfs2, },
  { rw [mul_comm (fs _ hx1), mul_assoc], apply hft2, },
end

lemma sUnion_contains_arith_progression (s : set (set ℤ)) 
  (hs : ∀ i ∈ s, contains_arith_progression i) : contains_arith_progression (⋃₀ s) :=
begin 
  rintros x ⟨i, hi1, hi2⟩,
  obtain ⟨m, hm1, hm2⟩ := hs i hi1 x hi2,
  refine ⟨m, hm1, λ k, set.mem_sUnion_of_mem (hm2 k) hi1⟩,
end

instance weird_top_on_int : topological_space ℤ :=
{ is_open := contains_arith_progression,
  is_open_univ := univ_contains_arith_progression,
  is_open_inter := inter_contains_arith_progression,
  is_open_sUnion := sUnion_contains_arith_progression }

lemma is_open_iff_weird (s : set ℤ) : is_open s ↔ contains_arith_progression s := iff.rfl

lemma nonempty_open_is_infinite (s : set ℤ) (hs1 : is_open s) (hs2 : s.nonempty) :
  s.infinite :=
begin 
  rw is_open_iff_weird at hs1,
  cases hs2 with x hx,
  obtain ⟨m, hm1, hm2⟩ := hs1 x hx,
  set f : ℤ → s := λ z, ⟨_, hm2 z⟩ with f_eq,
  haveI infinite1 := infinite.of_injective f _,
  work_on_goal 2 
  { rintros a b hab,
    rw [f_eq, subtype.ext_iff_val] at hab,
    dsimp only at hab,
    rwa [add_left_inj, mul_right_inj'] at hab,
    linarith, },
  rwa set.infinite_coe_iff at infinite1,
end

def arith_progression (a m : ℤ) := {z : ℤ | ∃ k, m * k + a = z }

lemma arith_progression_open (a m : ℤ) (hm : 1 ≤ m) : is_open (arith_progression a m) :=
begin 
  rw is_open_iff_weird,
  rintros _ ⟨k, rfl⟩,
  exact ⟨m, hm, λ k', ⟨k + k', by ring⟩⟩,
end

lemma arith_progression_closed (a m : ℤ) (hm : 1 ≤ m) : is_closed (arith_progression a m) :=
begin 
  rw [←is_open_compl_iff, is_open_iff_weird],
  intros x hx,
  rw [arith_progression, set.mem_compl_iff, set.mem_set_of_eq, not_exists] at hx,
  refine ⟨m, hm, λ k r, _⟩,
  obtain ⟨k', hk'⟩ := r,
  
  refine hx (k' - k) _,
  rw [←sub_eq_zero] at hk' ⊢,
  rw ←hk', 
  ring,
end

lemma arith_progression_clopen (a m : ℤ) (hm : 1 ≤ m) :
  is_clopen (arith_progression a m) :=
{ left := arith_progression_open _ _ hm,
  right := arith_progression_closed _ _ hm }

def prime_int : Type := subtype (prime : ℤ → Prop) 

lemma seteq1 : 
(⋃ (p : ℕ) (hp : nat.prime p), arith_progression 0 p)ᶜ = 
{1, -1} :=
begin 
  classical,
  ext1 x,
  split,
  { intros hx,
    simp only [set.mem_compl_iff, set.mem_Union, not_exists, add_zero, 
      set.mem_set_of_eq] at hx,
    by_cases ne0 : x = 0,
    { rw ne0 at *,
      exfalso,
      specialize hx 2 nat.prime_two,
      refine hx ⟨0, by norm_num⟩, },
    
    by_contra r,
    simp only [set.mem_insert_iff, set.mem_singleton_iff, not_or_distrib] at r,
    have ineq1 : x.nat_abs ≠ 1,
    { intros rid, rw [int.nat_abs_eq_iff, show (↑(1 : ℕ) : ℤ) = 1, from rfl] at rid, tauto, },
    
    specialize hx (x.nat_abs.min_fac) (nat.min_fac_prime ineq1),
    obtain ⟨r, hr⟩ := x.nat_abs.min_fac_dvd,
    rcases int.nat_abs_eq x with (hx'|hx'),
    { refine hx ⟨r, _⟩,
      rw [add_zero],
      conv_rhs { rw [hx'] },
      exact_mod_cast hr.symm, },
    { refine hx _,
      refine ⟨-r, _⟩,
      replace hx' := hx'.symm,
      rw [neg_eq_iff_eq_neg] at hx',
      rw [add_zero, mul_neg, neg_eq_iff_eq_neg, ← hx'],
      exact_mod_cast hr.symm, }, },
  { intros r,
    simp only [set.mem_insert_iff, set.mem_singleton_iff] at r,
    rcases r with (rfl|rfl),
    all_goals 
    { simp_rw [set.mem_compl_iff, set.mem_Union, arith_progression, set.mem_set_of_eq, add_zero],
      push_neg,
      intros i hi1 k r,
      try { rw int.mul_eq_one_iff_eq_one_or_neg_one at r },
      try { rw int.mul_eq_neg_one_iff_eq_one_or_neg_one at r },
      rcases r with (⟨hi, rfl⟩|⟨hi, rfl⟩),
      { norm_cast at hi,
        rw hi at hi1,
        exact nat.not_prime_one hi1, },
      { have := int.coe_nat_nonneg i, linarith, }, }, },
end

lemma not_closed : ¬ is_closed (⋃ (p : ℕ) (hp : nat.prime p), arith_progression 0 p) :=
begin 
  rw [←is_open_compl_iff.not, seteq1],
  intro r,
  have h1 := nonempty_open_is_infinite {1, -1} r ⟨1, by simp⟩,
  have h2 : ({1, -1} : set ℤ).finite := by simp,
  rw ←set.not_infinite at h2,
  exact h2 h1,
end

lemma not_closed' :  ¬ is_closed (⋃ (p : set_of nat.prime), arith_progression 0 (p : ℤ)) :=
begin 
  simp only [coe_coe, set.mem_set_of_eq, subtype.coe_mk, set.Union_coe_set],
  exact not_closed,
end

lemma infinite_prime : (set_of nat.prime).infinite :=
begin 
  by_contra r,
  rw set.not_infinite at r,
  refine not_closed' _,
  haveI : finite (set_of nat.prime),
  { exact set.finite_coe_iff.mpr r, },
  refine is_closed_Union (λ i, arith_progression_closed _ _ _),
  norm_cast, 
  linarith [show (2 : ℕ) ≤ i, by exact_mod_cast nat.prime.two_le i.2],
end
