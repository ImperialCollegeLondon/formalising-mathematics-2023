import tactic
import data.zmod.basic
import field_theory.finite.basic
import data.nat.prime_norm_num

/-

# Prove the theorem, due to Kraichik, asserting that 13|2^70+3^70

This is the sixth question in Sierpinski's book "250 elementary problems
in number theory".

-/

example : 13 ∣ 2^70 + 3^70 :=
begin
  -- use a computer algebra package to work out (2^70+3^70)/13
  use 192550423461109399456637645953021,
  norm_num,
end

-- Here is a more honest proof, using Fermat's Little Theorem
example : 13 ∣ 2^70 + 3^70 :=
begin
  -- reduce to a question about `zmod 13`
  rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd,
  -- get rid of the arrows
  push_cast, -- oops that did some weird stuff
  -- fix up the goal
  change (2 : zmod 13) ^ 70 + (3 : zmod 13) ^ 70 = 0,
  have h0 : nat.prime 13 := by norm_num,
  haveI : fact (nat.prime 13) := ⟨h0⟩,
  -- apply Fermat's Little Theorem
  have h1 : (2 : zmod 13)^12 = 1,
  { apply zmod.pow_card_sub_one_eq_one,
    intro h2,
    have h3 : ((2 : ℕ) : zmod 13) = 0,
      assumption_mod_cast,
    rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h3,
    revert h3,
    norm_num,
  },
  -- For 3 we can do better
  have h2 : (3 : zmod 13)^3 = 1,
    refl,
  -- use `conv` mode to rewrite the `70`s in the goal
  conv_lhs begin
    congr,
    rw (show 70 = 12 * 5 + 10, by norm_num),
    skip,
    rw (show 70 = 3 * 23 + 1, by norm_num),
  end,
  -- now use Fermat's Little Theorem to simplify
  rw [pow_add, pow_add, pow_mul, pow_mul, h1, h2],
  simp,
  -- We still have to work out 2^10 though, so 
  -- in some sense we're still doing a calculation, just
  -- a smaller one
  norm_num,
  refl, -- lol, funny way to finish (these are numbers mod 13)
end
