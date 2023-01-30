/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import group_theory.quotient_group -- import Lean's quotient groups

/-

# Quotient groups

mathlib has quotient groups. Here's how they work.

-/

-- let G be a group and let N be a normal subgroup
variables (G : Type) [group G] (N : subgroup G) [subgroup.normal N]

-- The underlying type (or set) of the quotient group. Note that `⧸` is `\quot`, not the slash
-- character `/` in your keyboard.

example : Type := G ⧸ N

-- Let's check that the typeclass inference system can find the group structure on the quotient
example : group (G ⧸ N) := infer_instance

-- The group homomorphism from `G` to `G ⧸ N`

example : G →* G ⧸ N := quotient_group.mk' N

-- Remarks:
-- (1) Why `quotient_group.mk'` and not `quotient_group.mk`? Because the version without the `'`
-- is just the function, the version with the `'` is the group homomorphism.
-- (2) Why does `quotient_group.mk' N` want to have `N` as an input but not `G`? It's because
-- the type of `N` is `subgroup G` so Lean can figure out `G` from `N`: if you like, `N` "knows
-- which group it's a subgroup of".

-- Here is the basic API you need for quotient groups.

-- the map G → G ⧸ N is surjective
example : function.surjective (quotient_group.mk' N) := quotient_group.mk'_surjective N 

-- Two elements of G have the same image in `G ⧸ N` iff they differ by an element of `N`
example (x y : G) : quotient_group.mk' N x = quotient_group.mk' N y ↔ ∃ n ∈ N, x * n = y :=
quotient_group.mk'_eq_mk' N

-- There is of course much more API, but if you want to get some practice you can
-- just develop some of it yourself from these two functions.

example : (quotient_group.mk' N).ker = N :=
begin
  ext a,
  rw monoid_hom.mem_ker,
  have h : quotient_group.mk' N 1 = 1 := monoid_hom.map_one _,
  rw [← h, eq_comm, quotient_group.mk'_eq_mk'],
  -- now it's just `one_mul` and logic
  simp,
end

-- The "universal property" of quotients says that if you have a group homomorphism `φ : G →* H`
-- whose kernel contains `N` then it "extends" to a group homomorphism `ψ : G ⧸ N →* H`
-- such that the composite map `ψ ∘ (quotient_group.mk' N)` equals `φ`. Given `φ`, the `ψ` with
-- this property is called `quotient_group.lift N φ h`, where `h` is a proof of `∀ x, x ∈ N → φ x = 1`.

variables (H : Type) [group H] (φ : G →* H) (h : ∀ x, x ∈ N → φ x = 1)

example : G ⧸ N →* H := quotient_group.lift N φ h

-- The proof that if `x : G` then `(quotient_group.lift N φ h) ((quotient_group.mk' N) x) = φ x`
-- is, amazingly, `refl`. 

example (x : G) : (quotient_group.lift N φ h) ((quotient_group.mk' N) x) = φ x :=
begin
  refl,
end

-- Technical remark: this would not be the case if quotient groups were *defined* to 
-- be cosets. In Lean quotient groups are an *opaque definition*. What do I mean by this? 
-- You probably learnt in algebra that if G is a group and H is a normal subgroup then the 
-- quotient G⧸H has elements which are *equal* to cosets of H. In Lean this is not true.
-- A term of the quotient type G⧸H cannot be taken apart with `cases` because it is not *equal* to
-- a coset. But the universal property `quotient_group.lift` is all we need; we don't
-- need to worry about the underlying definition of the quotient.

-- Example. Let's use `quotient_group.lift` to define the following map. Say `φ : G →* H` is a 
-- group hom and we have normal subgroups `N : subgroup G` and `P : subgroup H` such that `φ N ≤ P`.
-- Then the induced map `G →* H ⧸ P` has `N` in the kernel, so it "lifts" to a group hom
-- `ρ : G ⧸ N →* H ⧸ P` with the property that for all `x : G`, 
-- `ρ (quotient_group.mk' N x) = quotient_group.mk' P (φ x)`. Let's define `ρ` and prove
-- this equality.

variables {G H φ N} {P : subgroup H} 
variable [P.normal]

def ρ (h : N.map φ ≤ P) : G ⧸ N →* H ⧸ P := 
quotient_group.lift N ((quotient_group.mk' P).comp φ) 
begin
  -- we are using `quotient_group.lift` so we need to supply the proof that `(mk' P).comp φ` kills `N`
  intros g hg,
  -- the simplifier can help out with this mess:
  suffices : φ g ∈ P,
  { simpa, },
  apply h,
  use g,
  exact ⟨hg, rfl⟩,
end

-- Now let's prove that `ρ ∘ mk' N = mk' P ∘ φ`

/-
    G ----φ----> H
    |            |
    |            |
   mk'           mk' 
    |            |
    \/           \/
  G ⧸ N --ρ--> H ⧸ P

-/
open quotient_group -- no idea why I didn't do this earlier

example (h : N.map φ ≤ P) (x : G) : ρ h (mk' N x) = mk' P (φ x) :=
begin
  -- this proof does my head in
  refl,
end
