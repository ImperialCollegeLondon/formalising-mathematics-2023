/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/

import topology.bases               -- definition of topological bases
import topology.metric_space.basic  -- facts about intervals in ℝ
import topology.algebra.order.floor -- facts about floor function, fractional part function etc

namespace section10sheet1

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

open topological_space

variables (X : Type u)

/--
The discrete topology is the one the most open sets.
-/
def discrete : topological_space X :=
sorry

/--
The indiscrete topology is the one with the least open sets.
-/
def indiscrete : topological_space X :=
sorry

/--
                `1`
`(X, discrete) ----->  (X, indiscrete)` is continuous 
-/
example : @@continuous (discrete X) (indiscrete X) id :=
sorry
/--
But is
                   `1`
`(X, indiscrete) ------> (X, discrete)` continuous?
-/
example (x y : X) (h : x ≠ y) : ¬ @@continuous (indiscrete X) (discrete X) id :=
sorry


/--
Finite sets only have finitely many possible topology on them.
-/
instance finitely_many_topologies [fintype X] : fintype (topological_space X) :=
sorry
/--
The upper bound is 2^2^|X|
-/
lemma card_topology_le [fintype X] : 
  fintype.card (topological_space X) ≤ 2 ^ (2 ^ fintype.card X):=
sorry

/--
`ℝ` has a basis consisted of all open intervals
-/
example : is_topological_basis { I | ∃ (a b : ℝ), I = set.Ioo a b } :=
sorry

/--
`ℚ ⊆ ℝ` is dense
-/
lemma dense_ℚ : dense (algebra_map ℚ ℝ '' set.univ) :=
sorry

/--
Hence functions `ℝ → ℝ` is uniquely determined on `ℚ`.
-/
example (f g : ℝ → ℝ) (hf : continuous f) (hg : continuous g) 
  (heq : ∀ (x : ℚ), f x = g x) : f = g :=
sorry

/--
An algebraic interpretation of unit circle `S¹` defined as `ℝ ⧸ ℤ` with the quotient topology,
i.e. `V ⊆ S¹` is open iff `π ⁻¹ V` is open in `ℝ` where `π : ℝ → ℝ ⧸ ℤ`.
-/
@[derive [topological_space, add_comm_group, inhabited]]
def circle := ℝ ⧸ (algebra_map ℤ ℝ).to_add_monoid_hom.range

namespace circle

/-- π -/
def from_real : ℝ → circle := sorry

/-- `[0, 1) → ℝ → S¹` -/
def from_Ico : set.Ico (0 : ℝ) 1 → circle := sorry

@[continuity]
lemma continuous_from_real : continuous from_real := sorry

@[continuity]
lemma continuous_on_from_real : continuous_on from_real (set.Ico 0 1) := sorry

@[continuity]
lemma continuous_from_Ico : continuous from_Ico :=
sorry

lemma from_Ico_inj : function.injective from_Ico :=
sorry

lemma from_Ico_surj : function.surjective from_Ico :=
sorry

/--
`S¹` is compact.
-/
instance is_compact : compact_space circle :=
sorry

/--
The half open interval `[0, 1)` continuously bijects to `S¹`.
-/
def equiv_Ico : set.Ico (0 : ℝ) 1 ≃ circle :=
sorry
/--
However, its inverse is not continuous.
-/
lemma not_cont_inv : ¬ continuous equiv_Ico.symm :=
sorry

end circle

end section10sheet1