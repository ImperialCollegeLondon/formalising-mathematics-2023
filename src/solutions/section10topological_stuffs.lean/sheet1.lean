/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/

import topology.bases               -- definition of topological bases
import topology.metric_space.basic  -- facts about intervals in ℝ
import topology.algebra.order.floor -- facts about floor function, fractional part function etc

noncomputable theory

/-!

# Topological Spaces in Lean

For any `X : Type`, a topology on `X` is defined as:
```
@[protect_proj] structure topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))
```

In this sheet, the following can be found:
- defining several topological spaces;
- proof or disproof of some functions being continuous;
- denseness, compactness;
- homeomorphism
-/

universe u

namespace topological_space

variables (X : Type u)

/--
The discrete topology is the one the most open sets.
-/
def discrete : topological_space X :=
{ is_open := λ _, true,
  is_open_univ := ⟨⟩,
  is_open_inter := λ _ _ _ _, ⟨⟩,
  is_open_sUnion := λ _ _, ⟨⟩ }

/--
The indiscrete topology is the one with the least open sets.
-/
def indiscrete : topological_space X :=
{ is_open := λ s, s = set.univ ∨ s = ∅,
  is_open_univ := or.intro_left _ rfl,
  is_open_inter := by rintros _ _ (rfl|rfl) (rfl|rfl); simp,
  is_open_sUnion := 
  begin 
    intros S h,
    by_cases h' : set.univ ∈ S,
    { left,
      refine le_antisymm (λ _ _, ⟨⟩) (λ x _, _),
      rw [set.mem_sUnion],
      refine ⟨_, h', ⟨⟩⟩, },
    { right,
      simp_rw [set.eq_empty_iff_forall_not_mem, set.mem_sUnion],
      push_neg,
      rintros _ s hs,
      exact (h s hs).elim (λ H, false.elim $ h' $ by rwa H at hs) 
        (λ H, H.symm ▸ id), },
  end }

/--
                `1`
`(X, discrete) ----->  (X, indiscrete)` is continuous 
-/
example : @@continuous (discrete X) (indiscrete X) id :=
{ is_open_preimage := λ _ _, ⟨⟩ }

/--
But is
                   `1`
`(X, indiscrete) ------> (X, discrete)` continuous?
-/
example (x y : X) (h : x ≠ y) : ¬ @@continuous (indiscrete X) (discrete X) id :=
begin 
  rw continuous_def,
  push_neg,
  refine ⟨{x}, ⟨⟩, not_or (_ : _ ≠ _) $ λ r, set.eq_empty_iff_forall_not_mem.mp r x rfl⟩,
  rw set.ne_univ_iff_exists_not_mem,
  refine ⟨y, λ r', h (set.mem_singleton_iff.mp (set.mem_preimage.mp r')).symm⟩,
end

/--
Finite sets only have finitely many possible topology on them.
-/
instance finitely_many_topologies [fintype X] : fintype (topological_space X) :=
let i : topological_space X → set (set X) := λ τ, τ.is_open in
have inj_i : function.injective i, by { intros τ1 τ2 h, ext1, exact h },
begin 
  haveI : fintype (set (set X)) := infer_instance,
  exact fintype.of_injective i inj_i,
end

/--
The upper bound is 2^2^|X|
-/
lemma card_topology_le [fintype X] : 
  fintype.card (topological_space X) ≤ 2 ^ (2 ^ fintype.card X):=
let i : topological_space X → set (set X) := λ τ, τ.is_open in
have inj_i : function.injective i, by { intros τ1 τ2 h, ext1, exact h },
begin 
  refine le_trans (fintype.card_le_of_injective i inj_i) _,
  rw [fintype.card_set, fintype.card_set],
end

/--
`ℝ` has a basis consisted of all open intervals
-/
example : is_topological_basis { I | ∃ (a b : ℝ), I = set.Ioo a b } :=
is_topological_basis_of_open_of_nhds 
  (by { rintros _ ⟨a, b, rfl⟩, rw real.Ioo_eq_ball, exact metric.is_open_ball }) $ 
λ x s hx hs, 
begin
  rw metric.is_open_iff at hs,
  obtain ⟨ε, hε, subset1⟩ := hs x hx,
  rw real.ball_eq_Ioo at subset1,
  exact ⟨_, ⟨_, _, rfl⟩, ⟨show x - ε < x, by linarith, by linarith⟩, subset1⟩,
end

/--
`ℚ ⊆ ℝ` is dense
-/
lemma dense_ℚ : dense (algebra_map ℚ ℝ '' set.univ) :=
begin 
  intros x,
  rw mem_closure_iff,
  intros v hv hx,
  rw metric.is_open_iff at hv,
  specialize hv x hx,
  obtain ⟨ε, hε, subset1⟩ := hv,
  rw real.ball_eq_Ioo at subset1,
  obtain ⟨q, hq⟩ := exists_rat_near x hε,
  rw abs_lt at hq,
  cases hq,
  refine ⟨q, subset1 ⟨_, _⟩, ⟨_, ⟨⟩, rfl⟩⟩;
  linarith,
end

/--
Hence functions `ℝ → ℝ` is uniquely determined on `ℚ`.
-/
example (f g : ℝ → ℝ) (hf : continuous f) (hg : continuous g) 
  (heq : ∀ (x : ℚ), f x = g x) : f = g :=
continuous.ext_on dense_ℚ hf hg $ λ _ ⟨q, ⟨⟩, h⟩, h ▸ heq q

/--
An algebraic interpretation of unit circle `S¹` defined as `ℝ ⧸ ℤ` with the quotient topology,
i.e. `V ⊆ S¹` is open iff `π ⁻¹ V` is open in `ℝ` where `π : ℝ → ℝ ⧸ ℤ`.
-/
@[derive [topological_space, add_comm_group, inhabited]]
def circle := ℝ ⧸ (algebra_map ℤ ℝ).to_add_monoid_hom.range

namespace circle

/-- π -/
def from_real : ℝ → circle := quotient.mk'

/-- `[0, 1) → ℝ → S¹` -/
def from_Ico : set.Ico (0 : ℝ) 1 → circle :=
from_real ∘ subtype.val

@[continuity]
lemma continuous_from_real : continuous from_real := ⟨λ _, id⟩

@[continuity]
lemma continuous_on_from_real : continuous_on from_real (set.Ico 0 1) := 
continuous.continuous_on ⟨λ s, id⟩

@[continuity]
lemma continuous_from_Ico : continuous from_Ico :=
begin 
  rw continuous_iff_continuous_on_univ,
  refine continuous_on.comp _ _ _,
  { exact set.Ico 0 1 },
  { exact continuous_on_from_real },
  { refine continuous.continuous_on _, continuity, },
  { intros x hx, exact x.2, },
end

lemma from_Ico_inj : function.injective from_Ico :=
begin 
  rintros ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩ h,
  dsimp only [from_Ico, from_real, function.comp_apply] at h,
  rw [quotient.eq', quotient_add_group.left_rel_eq] at h,
  obtain ⟨z, (hz : ↑z = -(x : ℝ) + y)⟩ := h,
  rw neg_add_eq_sub at hz,
  have ineq1 : abs (y - x : ℝ) < 1,
  { rw abs_lt, split; linarith, },
  rw ←hz at ineq1,
  norm_cast at ineq1,
  rw int.abs_lt_one_iff at ineq1,
  rw ineq1 at hz,
  norm_cast at hz,
  replace hz := hz.symm,
  rw sub_eq_zero at hz,
  simp_rw hz,
  refl,
end

lemma from_Ico_surj : function.surjective from_Ico :=
begin 
  intros x,
  induction x using quotient.induction_on',
  dsimp only [from_Ico, from_real, function.comp_apply],
  refine ⟨⟨int.fract x, int.fract_nonneg _, int.fract_lt_one _⟩, _⟩,
  rw quotient.eq',
  rw [quotient_add_group.left_rel_eq, neg_add_eq_sub, int.self_sub_fract],
  exact ⟨_, rfl⟩,
end

/--
`S¹` is compact.
-/
instance is_compact : compact_space circle :=
{ is_compact_univ := 
  begin 
    rw show set.univ = from_real '' (set.Icc 0 1), from _,
    { exact is_compact.image is_compact_Icc ⟨λ s h, h⟩, },
    symmetry,
    rw set.eq_univ_iff_forall,
    intros x,
    induction x using quotient.induction_on',
    dsimp only [from_Ico, from_real, function.comp_apply],
    refine ⟨int.fract x, ⟨int.fract_nonneg _, le_of_lt $ int.fract_lt_one _⟩, _⟩,
    rw quotient.eq',
    rw [quotient_add_group.left_rel_eq, neg_add_eq_sub, int.self_sub_fract],
    exact ⟨_, rfl⟩,
  end }

/--
The half open interval `[0, 1)` continuously bijects to `S¹`.
-/
def equiv_Ico : set.Ico (0 : ℝ) 1 ≃ circle :=
equiv.of_bijective from_Ico ⟨from_Ico_inj, from_Ico_surj⟩

/--
However, its inverse is not continuous.
-/
lemma not_cont_inv : ¬ continuous equiv_Ico.symm :=
have nc : ¬ compact_space (set.Ico (0 : ℝ) 1),
begin 
  intros r,
  have seteq : (subtype.val : set.Ico (0 : ℝ) 1 → ℝ) '' set.univ = set.Ico 0 1,
  { refine set.ext (λ x, ⟨_, _⟩),
    { rintros ⟨y, ⟨⟨⟩, rfl⟩⟩, exact y.2 },
    { rintros ⟨hx1, hx2⟩, exact ⟨⟨x, hx1, hx2⟩, ⟨⟩, rfl⟩, }, },
  have c' : is_compact (set.Ico (0 : ℝ) 1),
  { rw ←seteq, exact r.1.image (by continuity), },
  have c'' := c'.is_closed.closure_eq,
  rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1), set.ext_iff] at c'',
  linarith [((c'' 1).mp ⟨zero_le_one, le_refl _⟩).2],
end,
begin
  contrapose! nc,
  let i : homeomorph (set.Ico (0 : ℝ) 1) circle := 
  { continuous_to_fun := by continuity,
    continuous_inv_fun := nc, ..equiv_Ico },
  exact i.symm.compact_space,
end

end circle

end topological_space
