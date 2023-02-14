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
begin 
  rw set.eq_empty_iff_forall_not_mem,
  intros p,
  rw [mem_V, set.univ_subset_iff],
  have mem1 : (1 : R) ∉ (p.as_ideal : set R) := p.as_ideal.ne_top_iff_one.mp p.is_prime.ne_top,
  intros r,
  rw r at mem1,
  exact mem1 ⟨⟩,
end

/--
R is zero locus of `∅`
-/
lemma V_empty : V (∅ : set R) = set.univ :=
set.eq_univ_iff_forall.mpr $ λ p x r, false.elim $ (set.mem_empty_iff_false _).mp r

/--
union of zero loci is zero locus of pointwise product
-/
lemma V_union (s t : set R) : V s ∪ V t = V (s * t) :=
begin 
  ext p,
  split,
  { rintros (hp|hp);
    rw mem_V at hp ⊢;
    intros r hr;
    obtain ⟨a, b, ha, hb, rfl⟩ := hr,
    { specialize hp ha,
      exact p.as_ideal.mul_mem_right _ hp, },
    { specialize hp hb,
      exact p.as_ideal.mul_mem_left _ hp, }, },
  { intros hp,
    rw mem_V at hp,
    rw [set.mem_union, mem_V, mem_V],
    contrapose! hp,
    simp only [set.not_subset_iff_exists_mem_not_mem] at hp ⊢,
    obtain ⟨⟨a, ha1, ha2⟩, ⟨b, hb1, hb2⟩⟩ := hp,
    exact ⟨_, ⟨a, b, ha1, hb1, rfl⟩, λ r, (p.is_prime.mem_or_mem r).elim 
      (λ h, ha2 h) (λ h, hb2 h)⟩, },
end

/--
intersection of zero loci is zero locus of union
-/
lemma V_inter {ι : Sort*} (s : ι → set R) : 
  (⋂ i : ι, V (s i)) = V (⋃ i, (s i)) :=
begin 
  ext p, 
  split;
  intros hp,
  { simp_rw [set.mem_Inter, mem_V] at hp,
    rw [mem_V, set.Union_subset_iff],
    assumption, },
  { rw [mem_V, set.Union_subset_iff] at hp,
    simp_rw [set.mem_Inter, mem_V],
    assumption, },
end

end

instance Zariski_topology : topological_space (Spec R) :=
topological_space.of_closed 
{ t | ∃ (s : set R), t = V s } ⟨set.univ, V_univ.symm⟩ 
begin 
  rintros _ hS,
  choose a ha using hS,
  rw [set.sInter_eq_bInter],
  suffices : (⋂ (i : set (Spec R)) (h : i ∈ A), i) = ⋂ (i : A), V (a i.2),
  { rw [this, V_inter],
    exact ⟨_, rfl⟩, },
  simp only [subtype.val_eq_coe, subtype.coe_mk, set.Inter_coe_set],
  exact set.Inter_congr (λ s, set.Inter_congr $ λ hs, ha hs),
end
begin 
  rintros _ ⟨s, rfl⟩ _ ⟨t, rfl⟩,
  rw V_union,
  exact ⟨s * t, rfl⟩,
end

/--
open sets of Zariski topology are complement of zero loci
-/
lemma zt_is_open (s : set (Spec R)) : is_open s ↔ ∃ (t : set R), s = (V t)ᶜ :=
begin 
  change (∃ _, _) ↔ _,
  rw [exists_congr],
  exact λ a, by rw [eq_compl_comm, eq_comm],
end

section

variables {R S}

/--
Basic open sets
-/
def D (f : R) : set (Spec R) := (V {f})ᶜ

lemma mem_D (f : R) (p : Spec R) : p ∈ D f ↔ f ∉ p.as_ideal :=
begin 
  split;
  intros hp hf;
  rw [D, set.mem_compl_iff, mem_V, set.singleton_subset_iff] at hp <|>
  rw [mem_V, set.singleton_subset_iff] at hf;
  exact hp hf,
end

lemma open_D (f : R) : is_open (D f) :=
begin 
  rw [D, zt_is_open],
  exact ⟨_, rfl⟩,
end

/--
Basic open sets form a basis
-/
lemma D_is_basis : is_topological_basis (set.range (D : R → set (Spec R))) :=
is_topological_basis_of_open_of_nhds (by { rintros _ ⟨r, -, rfl⟩, exact open_D _ }) $ 
λ p s hp hs, begin
  simp only [set.mem_range, exists_prop, exists_exists_eq_and, mem_D],
  rw zt_is_open at hs,
  obtain ⟨s, rfl⟩ := hs,
  rw [set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem] at hp,
  obtain ⟨x, hx1, hx2⟩ := hp,
  refine ⟨x, hx2, λ y hy H, _⟩,
  exact (mem_D _ _).mp hy (H hx1),
end

/--
Ring homomorphisms induces continuous map (contravariantly).
-/
def comap (f : R →+* S) : Spec S → Spec R :=
λ p, ⟨p.as_ideal.comap f, infer_instance⟩

lemma comap_as_ideal (f : R →+* S) (p : Spec S) : (comap f p).as_ideal = p.as_ideal.comap f := rfl

lemma continuous_comap (f : R →+* S) : continuous (comap f) :=
begin 
  refine D_is_basis.continuous _ _,
  rintros _ ⟨r, rfl⟩,
  rw show comap f ⁻¹' D r  = D (f r),
  { ext1 p, 
    simp only [set.mem_preimage, mem_D, comap_as_ideal, ideal.mem_comap], },
  exact open_D _,
end

local notation `ℤ[X]` := (polynomial ℤ)
-- every thing from this points work for a generic integral domain
/--
the point corresponding to the zero ideal.
-/
@[simps]
noncomputable def η : Spec ℤ[X] :=
{ as_ideal := ⊥,
  is_prime := 
  { ne_top' := begin 
      rw [ideal.ne_top_iff_one, ideal.mem_bot],
      norm_num,
    end,
    mem_or_mem' := λ x y hxy, 
    begin 
      simp only [ideal.mem_bot] at hxy ⊢,
      rwa mul_eq_zero at hxy,
    end } }

/--
this is a generic point.
-/
lemma generic_η : closure {η} = (set.univ : set (Spec ℤ[X])) :=
begin 
  rw show closure {η} = V (η.as_ideal : set ℤ[X]),
  { ext,
    rw [mem_V, mem_closure_iff, η_as_ideal],
    split,
    { intros h r hr,
      rw [set_like.mem_coe, ideal.mem_bot] at hr,
      rw hr,
      exact ideal.zero_mem _, },
    { rintros - o ho hx,
      rw zt_is_open at ho,
      obtain ⟨o, rfl⟩ := ho,
      rw [set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem] at hx,
      obtain ⟨q, hq1, hq2⟩ := hx,
      by_cases q0 : q = 0,
      { rw [q0] at *,
        exfalso,
        refine hq2 (ideal.zero_mem _), },
      rw show (V o)ᶜ ∩ {η} = {η},
      { rw [set.inter_eq_right_iff_subset, set.singleton_subset_iff,
          set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem, η_as_ideal],
        exact ⟨q, hq1, q0⟩, },
      exact ⟨η, set.mem_singleton _⟩, }, },
  rw [η_as_ideal, set.eq_univ_iff_forall],
  intros x,
  rw [mem_V],
  intros y hy,
  rw [set_like.mem_coe, ideal.mem_bot] at hy,
  rw hy,
  exact ideal.zero_mem _,
end

/--
Generic points is unique.
-/
lemma generic_point_uniq (x : Spec ℤ[X]) (hx : closure {x} = (set.univ : set (Spec ℤ[X]))) :
  x = η :=
begin 
  have h : closure {x} = closure {η},
  { rw [generic_η, hx], },
  have H : ∀ (a b : Spec ℤ[X]), a.as_ideal ≤ b.as_ideal ↔ b ∈ closure {a},
  { intros a b,
    split,
    { rw mem_closure_iff,
      intros hle o ho hb,
      rw zt_is_open at ho,
      obtain ⟨o, rfl⟩ := ho,
      rw [set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem] at hb,
      obtain ⟨q, hq1, hq2⟩ := hb,
      rw [set.inter_nonempty], 
      simp_rw [set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem, 
        set_like.mem_coe],
      exact ⟨a, ⟨q, hq1, λ h, hq2 (hle h)⟩, set.mem_singleton _⟩, },
    { intros hmem p hp,
      rw [mem_closure_iff] at hmem,
      contrapose! hp,
      specialize hmem (D p) (open_D p) ((mem_D _ _).mpr hp),
      obtain ⟨x, hx1, hx2⟩ := hmem,
      rw set.mem_singleton_iff at hx2,
      rw hx2 at *,
      rwa mem_D at hx1, }, },
  have Hle1 : x.as_ideal ≤ η.as_ideal,
  { rw [H, h],
    exact subset_closure (set.mem_singleton _), },
  have Hle2 : η.as_ideal ≤ x.as_ideal,
  { rw [H, ←h],
    exact subset_closure (set.mem_singleton _), },
  ext1,
  exact le_antisymm Hle1 Hle2,
end

end
