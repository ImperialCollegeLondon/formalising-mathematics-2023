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
- if `f : R →+* S` is a ring homomorphism, then `𝔭 ↦ f⁻¹ 𝔭` is continuous. 
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
zero locus of a set `s ⊆ R` is the set of all prime ideals larger than `s`.

if `f : R`, then it defines a function `𝔭 ↦ ([f] : R ⧸ 𝔭)`.

So `V s` is exactly those primes
vanishing for all `f ∈ s`.
-/
def V (s : set R) : set (Spec R) :=
{ I : Spec R | s ⊆ I.as_ideal }

lemma mem_V (s : set R) {p : Spec R} : p ∈ V s ↔ s ⊆ p.as_ideal := 
iff.rfl

/--
empty set is zero locus of `R`
-/
lemma V_univ : V (set.univ : set R) = ∅ :=
sorry

/--
R is zero locus of `∅`
-/
lemma V_empty : V (∅ : set R) = set.univ :=
sorry

/--
union of zero loci is zero locus of pointwise product
-/
lemma V_union (s t : set R) : V s ∪ V t = V (s * t) :=
sorry

/--
intersection of zero loci is zero locus of union
-/
lemma V_inter {ι : Sort*} (s : ι → set R) : 
  (⋂ i : ι, V (s i)) = V (⋃ i, (s i)) := 
sorry

end

instance Zariski_topology : topological_space (Spec R) := sorry

/--
open sets of Zariski topology are complement of zero loci
-/
lemma zt_is_open (s : set (Spec R)) : is_open s ↔ ∃ (t : set R), s = (V t)ᶜ := sorry

section

variables {R S}

/--
Basic open sets
-/
def D (f : R) : set (Spec R) := (V {f})ᶜ

lemma mem_D (f : R) (p : Spec R) : p ∈ D f ↔ f ∉ p.as_ideal := sorry
lemma open_D (f : R) : is_open (D f) := sorry

/--
Basic open sets form a basis
-/
lemma D_is_basis : is_topological_basis (set.range (D : R → set (Spec R))) :=
sorry

/--
Ring homomorphisms induces continuous map (contravariantly).
-/
def comap (f : R →+* S) : Spec S → Spec R :=
sorry

lemma comap_as_ideal (f : R →+* S) (p : Spec S) : 
  (comap f p).as_ideal = p.as_ideal.comap f :=
sorry

lemma continuous_comap (f : R →+* S) : continuous (comap f) :=
sorry

local notation `ℤ[X]` := (polynomial ℤ)
-- every thing from this points work for a generic integral domain
/--
the point corresponding to the zero ideal.
-/
@[simps]
def η : Spec ℤ[X] :=
{ as_ideal := sorry,
  is_prime := sorry }

/--
this is a generic point.
-/
lemma generic_η : closure {η} = (set.univ : set (Spec ℤ[X])) :=
sorry

/--
Generic points is unique.
-/
lemma generic_point_uniq (x : Spec ℤ[X]) (hx : closure {x} = (set.univ : set (Spec ℤ[X]))) :
  x = η :=
sorry

end
