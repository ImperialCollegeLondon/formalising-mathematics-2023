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
- if `f : R â+* S` is a ring homomorphism, then `ð­ âŠ fâ»Â¹ ð­` is continuous. 
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
zero locus of a set `s â R` is the set of all prime ideals larger than `s`.

if `f : R`, then it defines a function `ð­ âŠ ([f] : R â§ž ð­)`.

So `V s` is exactly those primes
vanishing for all `f â s`.
-/
def V (s : set R) : set (Spec R) :=
{ I : Spec R | s â I.as_ideal }

lemma mem_V (s : set R) {p : Spec R} : p â V s â s â p.as_ideal := 
iff.rfl

/--
empty set is zero locus of `R`
-/
lemma V_univ : V (set.univ : set R) = â :=
begin 
  rw set.eq_empty_iff_forall_not_mem,
  intros p,
  rw [mem_V, set.univ_subset_iff],
  have mem1 : (1 : R) â (p.as_ideal : set R) := p.as_ideal.ne_top_iff_one.mp p.is_prime.ne_top,
  intros r,
  rw r at mem1,
  exact mem1 âšâ©,
end

/--
R is zero locus of `â`
-/
lemma V_empty : V (â : set R) = set.univ :=
set.eq_univ_iff_forall.mpr $ Î» p x r, false.elim $ (set.mem_empty_iff_false _).mp r

/--
union of zero loci is zero locus of pointwise product
-/
lemma V_union (s t : set R) : V s âª V t = V (s * t) :=
begin 
  ext p,
  split,
  { rintros (hp|hp);
    rw mem_V at hp â¢;
    intros r hr;
    obtain âša, b, ha, hb, rflâ© := hr,
    { specialize hp ha,
      exact p.as_ideal.mul_mem_right _ hp, },
    { specialize hp hb,
      exact p.as_ideal.mul_mem_left _ hp, }, },
  { intros hp,
    rw mem_V at hp,
    rw [set.mem_union, mem_V, mem_V],
    contrapose! hp,
    simp only [set.not_subset_iff_exists_mem_not_mem] at hp â¢,
    obtain âšâša, ha1, ha2â©, âšb, hb1, hb2â©â© := hp,
    exact âš_, âša, b, ha1, hb1, rflâ©, Î» r, (p.is_prime.mem_or_mem r).elim 
      (Î» h, ha2 h) (Î» h, hb2 h)â©, },
end

/--
intersection of zero loci is zero locus of union
-/
lemma V_inter {Î¹ : Sort*} (s : Î¹ â set R) : 
  (â i : Î¹, V (s i)) = V (â i, (s i)) :=
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
{ t | â (s : set R), t = V s } âšset.univ, V_univ.symmâ© 
begin 
  rintros _ hS,
  choose a ha using hS,
  rw [set.sInter_eq_bInter],
  suffices : (â (i : set (Spec R)) (h : i â A), i) = â (i : A), V (a i.2),
  { rw [this, V_inter],
    exact âš_, rflâ©, },
  simp only [subtype.val_eq_coe, subtype.coe_mk, set.Inter_coe_set],
  exact set.Inter_congr (Î» s, set.Inter_congr $ Î» hs, ha hs),
end
begin 
  rintros _ âšs, rflâ© _ âšt, rflâ©,
  rw V_union,
  exact âšs * t, rflâ©,
end

/--
open sets of Zariski topology are complement of zero loci
-/
lemma zt_is_open (s : set (Spec R)) : is_open s â â (t : set R), s = (V t)á¶ :=
begin 
  change (â _, _) â _,
  rw [exists_congr],
  exact Î» a, by rw [eq_compl_comm, eq_comm],
end

section

variables {R S}

/--
Basic open sets
-/
def D (f : R) : set (Spec R) := (V {f})á¶

lemma mem_D (f : R) (p : Spec R) : p â D f â f â p.as_ideal :=
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
  exact âš_, rflâ©,
end

/--
Basic open sets form a basis
-/
lemma D_is_basis : is_topological_basis (set.range (D : R â set (Spec R))) :=
is_topological_basis_of_open_of_nhds (by { rintros _ âšr, -, rflâ©, exact open_D _ }) $ 
Î» p s hp hs, begin
  simp only [set.mem_range, exists_prop, exists_exists_eq_and, mem_D],
  rw zt_is_open at hs,
  obtain âšs, rflâ© := hs,
  rw [set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem] at hp,
  obtain âšx, hx1, hx2â© := hp,
  refine âšx, hx2, Î» y hy H, _â©,
  exact (mem_D _ _).mp hy (H hx1),
end

/--
Ring homomorphisms induces continuous map (contravariantly).
-/
def comap (f : R â+* S) : Spec S â Spec R :=
Î» p, âšp.as_ideal.comap f, infer_instanceâ©

lemma comap_as_ideal (f : R â+* S) (p : Spec S) : (comap f p).as_ideal = p.as_ideal.comap f := rfl

lemma continuous_comap (f : R â+* S) : continuous (comap f) :=
begin 
  refine D_is_basis.continuous _ _,
  rintros _ âšr, rflâ©,
  rw show comap f â»Â¹' D r  = D (f r),
  { ext1 p, 
    simp only [set.mem_preimage, mem_D, comap_as_ideal, ideal.mem_comap], },
  exact open_D _,
end

local notation `â€[X]` := (polynomial â€)
-- every thing from this points work for a generic integral domain
/--
the point corresponding to the zero ideal.
-/
@[simps]
noncomputable def Î· : Spec â€[X] :=
{ as_ideal := â¥,
  is_prime := 
  { ne_top' := begin 
      rw [ideal.ne_top_iff_one, ideal.mem_bot],
      norm_num,
    end,
    mem_or_mem' := Î» x y hxy, 
    begin 
      simp only [ideal.mem_bot] at hxy â¢,
      rwa mul_eq_zero at hxy,
    end } }

/--
this is a generic point.
-/
lemma generic_Î· : closure {Î·} = (set.univ : set (Spec â€[X])) :=
begin 
  rw show closure {Î·} = V (Î·.as_ideal : set â€[X]),
  { ext,
    rw [mem_V, mem_closure_iff, Î·_as_ideal],
    split,
    { intros h r hr,
      rw [set_like.mem_coe, ideal.mem_bot] at hr,
      rw hr,
      exact ideal.zero_mem _, },
    { rintros - o ho hx,
      rw zt_is_open at ho,
      obtain âšo, rflâ© := ho,
      rw [set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem] at hx,
      obtain âšq, hq1, hq2â© := hx,
      by_cases q0 : q = 0,
      { rw [q0] at *,
        exfalso,
        refine hq2 (ideal.zero_mem _), },
      rw show (V o)á¶ â© {Î·} = {Î·},
      { rw [set.inter_eq_right_iff_subset, set.singleton_subset_iff,
          set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem, Î·_as_ideal],
        exact âšq, hq1, q0â©, },
      exact âšÎ·, set.mem_singleton _â©, }, },
  rw [Î·_as_ideal, set.eq_univ_iff_forall],
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
lemma generic_point_uniq (x : Spec â€[X]) (hx : closure {x} = (set.univ : set (Spec â€[X]))) :
  x = Î· :=
begin 
  have h : closure {x} = closure {Î·},
  { rw [generic_Î·, hx], },
  have H : â (a b : Spec â€[X]), a.as_ideal â€ b.as_ideal â b â closure {a},
  { intros a b,
    split,
    { rw mem_closure_iff,
      intros hle o ho hb,
      rw zt_is_open at ho,
      obtain âšo, rflâ© := ho,
      rw [set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem] at hb,
      obtain âšq, hq1, hq2â© := hb,
      rw [set.inter_nonempty], 
      simp_rw [set.mem_compl_iff, mem_V, set.not_subset_iff_exists_mem_not_mem, 
        set_like.mem_coe],
      exact âša, âšq, hq1, Î» h, hq2 (hle h)â©, set.mem_singleton _â©, },
    { intros hmem p hp,
      rw [mem_closure_iff] at hmem,
      contrapose! hp,
      specialize hmem (D p) (open_D p) ((mem_D _ _).mpr hp),
      obtain âšx, hx1, hx2â© := hmem,
      rw set.mem_singleton_iff at hx2,
      rw hx2 at *,
      rwa mem_D at hx1, }, },
  have Hle1 : x.as_ideal â€ Î·.as_ideal,
  { rw [H, h],
    exact subset_closure (set.mem_singleton _), },
  have Hle2 : Î·.as_ideal â€ x.as_ideal,
  { rw [H, âh],
    exact subset_closure (set.mem_singleton _), },
  ext1,
  exact le_antisymm Hle1 Hle2,
end

end
