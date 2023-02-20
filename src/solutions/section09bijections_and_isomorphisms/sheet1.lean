/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic

/-

# Bijections

Like finiteness, there are two ways to say that a function is bijective in Lean.
Furthermore, you will have heard of both of them, although it may well not
have occurred to you that these two ways were particularly different. It turns
out that one of them is more constructive than the other. Let's talk about
the nonconstructive (propositional) way of talking about bijections.

Let `X` and `Y` be types, and say `f : X → Y` is a function. 

-/

variables (X Y : Type) (f : X → Y)

-- The `Prop`-valued way of saying that `f` is bijective is simply
-- to say literally that `f` is bijective, i.e., injective and surjective.

example : Prop := function.bijective f

-- Because `f` is a function type, a little Lean hack introduced recently
-- actually enables you to use dot notation for this.

example : Prop := f.bijective 

-- The definition of `function.bijective f` is 
-- `function.injective f ∧ function.surjective f`, and the definitions of
-- injective and surjective are what you think they are.

example : f.bijective ↔ f.injective ∧ f.surjective :=
begin
  refl
end

example : f.bijective ↔ (∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂) ∧ 
  (∀ y : Y, ∃ x : X, f x = y) :=
begin
  refl
end

-- It's a theorem that `f` is bijective if and only if it has a two-sided
-- inverse. One way is not hard to prove: see if you can do it. Make
-- sure you know the maths proof first! If you can't do this then
-- please ask. There's lots of little Lean tricks which make this
-- question not too bad, but there are lots of little pitfalls too.

example : (∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id) → f.bijective :=
begin
  rintro ⟨g, hfg, hgf⟩,
  split,
  { -- injectivity
    intros a b h,
    -- want to get from `g ∘ f = id` to `∀ x, g (f x) = x`.
    -- Use `simp_rw` to rewrite under the binder.
    simp_rw [function.funext_iff, function.comp_apply] at hgf,
    -- `apply_fun` can change a hypothesis `x = y` to `g x = g y`.
    apply_fun g at h,
    -- now use `hgf` to turn `h` into `id a = id b`, and then
    -- use `h` to close the goal (note `id a` is definitionally `a`)
    rwa [hgf, hgf] at h, },
  { -- surjectivity
    intro y, 
    use g y, -- pretty much the only element of x available!
    -- instead of rewrites let's use `change`
    change (f ∘ g) y = id y,
    rw hfg, },
end

-- The other way is harder in Lean, unless you know about the `choose`
-- tactic. Given `f` and a proof that it's a bijection, how do you
-- prove the existence of a two-sided inverse `g`? You'll have to construct
-- `g`, and the `choose` tactic does this for you.
-- If `hfs` is a proof that `f` is surjective, try `choose g hg using hfs`.
example : f.bijective → ∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id :=
begin
  -- f is injective and surjective
  rintro ⟨hfi, hfs⟩,
  -- construct `g` a one-sided inverse (because `f` is surjective)
  choose g hg using hfs,
  -- now you have to use `hg` to prove both f ∘ g = id and g ∘ f = id
  use g,
  split,
  { -- f ∘ g is straightforward
    ext y, -- use functional extensionality
    exact hg y, },-- abuse of defeq
  { -- g ∘ f needs a trick
    ext x, 
    -- here we use injectivity
    apply hfi,
    -- and here we abuse definitional equality
    exact hg (f x), },
end

