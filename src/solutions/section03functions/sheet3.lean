/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-

# More on functions

Another question on the Imperial introduction to proof problem sheet on functions
is "If `f : X → Y` and `g : Y → Z` and `g ∘ f` is injective, is it true that `g` is injective?"
This is not true. A counterexample could be made by letting `X` and `Z` have one element, 
and letting `Y` have two elements; `f` and `g` are then not hard to write down. Let's
see how to do this in Lean by making inductive types `X`, `Y` and `Z` and functions
`f` and `g` which give an explicit counterexample.

-/

-- Let X be {a}
inductive X : Type
| a : X

-- in fact the term of type X is called `X.a`.

-- Let Y be {b,c}
inductive Y : Type
| b : Y
| c : Y

inductive Z : Type
| d : Z

-- Define f by f(X.a)=Y.b
def f : X → Y
| X.a := Y.b

-- define g by g(Y.b)=g(Y.c)=Z.d
def g : Y → Z
| Y.b := Z.d
| Y.c := Z.d

-- Here `Z` only has one term, so if `z : Z` then `cases z` only produces one goal,
-- namely "what you get if you change `z` to `Z.d`".
example (z : Z) : z = Z.d :=
begin
  cases z,
  refl,
end

lemma Yb_ne_Yc : Y.b ≠ Y.c :=
begin
  intro h, -- x ≠ y is definitionally equal to (x = y) → false
  cases h, -- no cases when they're equal!
end

lemma gYb_eq_gYc : g Y.b = g Y.c :=
begin
  -- they're both definitionally `Z.d`
  refl,
end


open function

lemma gf_injective : injective (g ∘ f) :=
begin
  -- use `rintro` trick to do `intro, cases` at the same time
  rintro ⟨_⟩ ⟨_⟩ h,
  refl,
end

-- This is a question on the IUM (Imperial introduction to proof course) function problem sheet.
-- Recall that if you have a hypothesis of the form `h : ∀ A, ...`, then `specialize h X`
-- will specialize `h` to the specific case `A = X`.
example : ¬ (∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), injective (ψ ∘ φ) → injective ψ) :=
begin
  intro h,
  specialize h X Y Z f g gf_injective gYb_eq_gYc,
  cases h,
end

-- You might want to make some sublemmas first.
lemma gf_surjective : surjective (g ∘ f) :=
begin
  intro z,
  use X.a,
  cases z,
  refl,
end

-- This is another one. 
example : ¬ (∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), surjective (ψ ∘ φ) → surjective φ) :=
begin
  intro h,
  specialize h X Y Z f g gf_surjective Y.c,
  rcases h with ⟨⟨_⟩, ⟨⟩⟩, -- this line does three `cases` at once.
end