/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/

import ring_theory.ideal.operations
import topology.algebra.polynomial
import topology.bases

/-!
# Prime spectrum of a ring and its Zariski topology

This files contains the following: 
- Zariski topology on the set of all prime ideals of any ring `R`.
- a basis for Zariski topology 
- if `f : R โ+* S` is a ring homomorphism, then `๐ญ โฆ fโปยน ๐ญ` is continuous. 
- for integral domains, there is a unique generic point.
-/

open topological_space
open_locale pointwise

universe u

variables (R S : Type u) [comm_ring R] [comm_ring S]

/--
`Spec R` is the set of prime ideals of `R`
-/
@[ext]
structure Spec : Type u := 
(as_ideal : ideal R)
(is_prime : as_ideal.is_prime)

attribute [instance] Spec.is_prime -- making sure class inference knows term of `Spec R` is prime

section

variable {R}

/--
zero locus of a set `s โ R` is the set of all prime ideals larger than `s`.

if `f : R`, then it defines a function `๐ญ โฆ ([f] : R โงธ ๐ญ)`.

So `V s` is exactly those primes
vanishing for all `f โ s`.
-/
def V (s : set R) : set (Spec R) :=
{ I : Spec R | s โ I.as_ideal }

lemma mem_V (s : set R) {p : Spec R} : p โ V s โ s โ p.as_ideal := 
iff.rfl

/--
empty set is zero locus of `R`
-/
lemma V_univ : V (set.univ : set R) = โ :=
sorry

/--
R is zero locus of `โ`
-/
lemma V_empty : V (โ : set R) = set.univ :=
sorry

/--
union of zero loci is zero locus of pointwise product
-/
lemma V_union (s t : set R) : V s โช V t = V (s * t) :=
sorry

/--
intersection of zero loci is zero locus of union
-/
lemma V_inter {ฮน : Sort*} (s : ฮน โ set R) : 
  (โ i : ฮน, V (s i)) = V (โ i, (s i)) := 
sorry

end

instance Zariski_topology : topological_space (Spec R) := sorry

/--
open sets of Zariski topology are complement of zero loci
-/
lemma zt_is_open (s : set (Spec R)) : is_open s โ โ (t : set R), s = (V t)แถ := sorry

section

variables {R S}

/--
Basic open sets
-/
def D (f : R) : set (Spec R) := (V {f})แถ

lemma mem_D (f : R) (p : Spec R) : p โ D f โ f โ p.as_ideal := sorry
lemma open_D (f : R) : is_open (D f) := sorry

/--
Basic open sets form a basis
-/
lemma D_is_basis : is_topological_basis (set.range (D : R โ set (Spec R))) :=
sorry

/--
Ring homomorphisms induces continuous map (contravariantly).
-/
def comap (f : R โ+* S) : Spec S โ Spec R :=
sorry

lemma comap_as_ideal (f : R โ+* S) (p : Spec S) : 
  (comap f p).as_ideal = p.as_ideal.comap f :=
sorry

lemma continuous_comap (f : R โ+* S) : continuous (comap f) :=
sorry

local notation `โค[X]` := (polynomial โค)
-- every thing from this points work for a generic integral domain
/--
the point corresponding to the zero ideal.
-/
@[simps]
def ฮท : Spec โค[X] :=
{ as_ideal := sorry,
  is_prime := sorry }

/--
this is a generic point.
-/
lemma generic_ฮท : closure {ฮท} = (set.univ : set (Spec โค[X])) :=
sorry

/--
Generic points is unique.
-/
lemma generic_point_uniq (x : Spec โค[X]) (hx : closure {x} = (set.univ : set (Spec โค[X]))) :
  x = ฮท :=
sorry

end
