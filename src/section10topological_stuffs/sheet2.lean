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
sorry

lemma inter_contains_arith_progression (s t : set ℤ) 
  (hs : contains_arith_progression s) (ht : contains_arith_progression t) :
  contains_arith_progression (s ∩ t) := sorry

lemma sUnion_contains_arith_progression (s : set (set ℤ)) 
  (hs : ∀ i ∈ s, contains_arith_progression i) : contains_arith_progression (⋃₀ s) :=
sorry

instance weird_top_on_int : topological_space ℤ :=
{ is_open := contains_arith_progression,
  is_open_univ := univ_contains_arith_progression,
  is_open_inter := inter_contains_arith_progression,
  is_open_sUnion := sUnion_contains_arith_progression }

lemma is_open_iff_weird (s : set ℤ) : is_open s ↔ contains_arith_progression s := iff.rfl

lemma nonempty_open_is_infinite (s : set ℤ) (hs1 : is_open s) (hs2 : s.nonempty) :
  s.infinite :=
sorry

def arith_progression (a m : ℤ) := {z : ℤ | ∃ k, m * k + a = z }

lemma arith_progression_open (a m : ℤ) (hm : 1 ≤ m) : is_open (arith_progression a m) :=
sorry

lemma arith_progression_closed (a m : ℤ) (hm : 1 ≤ m) : is_closed (arith_progression a m) :=
sorry

lemma arith_progression_clopen (a m : ℤ) (hm : 1 ≤ m) :
  is_clopen (arith_progression a m) :=
sorry

lemma seteq1 : (⋃ (p : ℕ) (hp : nat.prime p), arith_progression 0 p)ᶜ = {1, -1} :=
sorry

lemma not_closed : ¬ is_closed (⋃ (p : ℕ) (hp : nat.prime p), arith_progression 0 p) :=
sorry

lemma not_closed' : ¬ is_closed (⋃ (p : set_of nat.prime), arith_progression 0 (p : ℤ)) :=
sorry

lemma infinite_prime : (set_of nat.prime).infinite :=
sorry
