/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic
import ring_theory.unique_factorization_domain -- UFDs
import ring_theory.principal_ideal_domain -- PIDs
import data.mv_polynomial.comm_ring -- multivariable polys
import ring_theory.polynomial.basic
/-

# Unique Factorization Domains

Thanks to Yael on the Discord for explaining to me how to write "let R be a UFD"
in Lean! It looks like this.

-/

-- let R be a UFD
variables (R : Type) [comm_ring R] [is_domain R] [unique_factorization_monoid R]

/-

The reason we're seeing `unique_factorization_monoid` here is that 
the definition of unique factorization domain never mentions addition!
So it makes sense for monoids.

[I wrote some bumph in the other file]

-/

-- a PID is a UFD (so ℤ, k[X] etc are UFDs)
example (R : Type) [comm_ring R] [is_domain R] [is_principal_ideal_ring R] : 
  unique_factorization_monoid R := by apply_instance

-- multivariate polynomials over a field in a set of variables 
-- indexed by a (possibly infinite) index set I are a UFD
example (k : Type) [field k] (I : Type) : 
  unique_factorization_monoid (mv_polynomial I k) := infer_instance

/- 

Here's a theorem about UFDs.

The *height* of a prime ideal `P` in a commutative ring `R` is
the largest `n` such that there exists a strictly increasing
chain of prime ideals `P₀ ⊂ P₁ ⊂ ⋯ ⊂ Pₙ = P` (or +∞ if there
are chains of arbitrary length). The claim is that in a UFD,
all height one primes are principal. The proof: in an integral
domain...

-/

-- out of laziness we don't define height n primes in a general
-- commutative ring but just height one primes in an integral
-- domain
def is_height_one_prime {R : Type} [comm_ring R] [is_domain R] (P : ideal R) : Prop :=
  P.is_prime ∧ P ≠ 0 ∧ ∀ Q : ideal R, Q.is_prime ∧ Q < P → Q = 0

example (R : Type) [comm_ring R] [is_domain R] [unique_factorization_monoid R]
  (P : ideal R) : is_height_one_prime P → P.is_principal :=
begin
  rintro ⟨hPprime, hPnonzero, hht1⟩,
  -- P is nonzero so choose nonzero x ∈ P
  have foo : ∃ x ∈ P, x ≠ (0 : R),
  { by_contra' h,
    apply hPnonzero,
    
  },
  sorry,

end

