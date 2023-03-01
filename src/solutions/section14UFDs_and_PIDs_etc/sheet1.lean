/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import ring_theory.principal_ideal_domain -- theory of PIDs

/-

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/

variables (R : Type) [comm_ring R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain. 
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":

variables [is_principal_ideal_ring R] [is_domain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.

example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 :=
begin
  intros a b,
  apply eq_zero_or_eq_zero_of_mul_eq_zero, -- typeclass inference 
  -- magically extracts the assumption from `is_domain`
end

example : (0 : R) ≠ 1 :=
begin
  -- this is another consequence of being an integral domain
  apply zero_ne_one,
end

example (I : ideal R) : I.is_principal :=
begin
  -- typeclass inference system finds `is_principal_ideal_ring` and
  -- uses it automatically
  exact is_principal_ideal_ring.principal I,
end

example (I : ideal R) : ∃ j, I = ideal.span {j} :=
begin
  -- to make a term of type `is_principal I` you need to give one proof,
  -- but we still need to do `cases` or equivalent (I used `obtain` below)
  -- to get this proof out.
  obtain ⟨h⟩ := is_principal_ideal_ring.principal I,
  exact h,
end

-- product of two PIDs isn't a PID, but only becuase it's not a domain
example (A B : Type) [comm_ring A] [comm_ring B]
  [is_principal_ideal_ring A] [is_principal_ideal_ring B] : 
  is_principal_ideal_ring (A × B) :=
{ principal := begin
    intro I,
    obtain ⟨a, (hA : _ = ideal.span _)⟩ := is_principal_ideal_ring.principal (I.map (ring_hom.fst A B)),
    obtain ⟨b, (hB : _ = ideal.span _)⟩ := is_principal_ideal_ring.principal (I.map (ring_hom.snd A B)),
    use (a,b),
    ext,
    simp only [ideal.submodule_span_eq],
    rw ideal.mem_span_singleton,
    split,
    { intro h,
      have h1 : ring_hom.fst A B x ∈ I.map (ring_hom.fst A B),
      { apply ideal.mem_map_of_mem _ h, },
      rw [hA, ideal.mem_span_singleton] at h1,
      rcases h1 with ⟨r, hr⟩,
      have h2 : ring_hom.snd A B x ∈ I.map (ring_hom.snd A B),
      { apply ideal.mem_map_of_mem _ h, },
      rw [hB, ideal.mem_span_singleton] at h2,
      rcases h2 with ⟨s, hs⟩,
      use (r,s),
      change x = (a*r,b*s),
      rw [← hr, ← hs],
      simp only [ring_hom.coe_fst, ring_hom.coe_snd, prod.mk.eta],  
    },
    { rintro ⟨⟨r, s⟩, rfl⟩,
      have ha : a ∈ I.map (ring_hom.fst A B),
      { rw [hA, ideal.mem_span_singleton], },
      have hb : b ∈ I.map (ring_hom.snd A B),
      { rw [hB, ideal.mem_span_singleton], },
      rw ideal.mem_map_iff_of_surjective at ha hb,
      { rcases ha with ⟨⟨a, b'⟩, haI, rfl⟩,
        rcases hb with ⟨⟨a', b⟩, hbI, rfl⟩,
        suffices : (a,b) ∈ I,
        { exact ideal.mul_mem_right _ _ this, },
        convert I.add_mem (I.mul_mem_left (1,0) haI)
          (I.mul_mem_left (0,1) hbI);
        simp, },
      { intro a, use (a,0), refl, },
      { intro b, use (0,b), refl, },
    }
  end }