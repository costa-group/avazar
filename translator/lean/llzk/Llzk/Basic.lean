import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic

/- Configuration for ZK environment: the prime, number of bits, and
   some corresponding requirements
-/
structure ZKConfig where
  k : ℕ  -- number of bits
  p : ℕ  -- the prime number
  p_prime : p.Prime -- stating that p is a prime.
  p_fits : p < 2^k -- p must fit in k bits

/- Register that c.p is a prime number -/
instance (c : ZKConfig) : Fact c.p.Prime := ⟨c.p_prime⟩

/- Register that c.p is not zero, it is useful for some proofs  -/
instance (c : ZKConfig) : NeZero c.p := ⟨c.p_prime.ne_zero⟩

/- Register that c.k is not zero, it is useful for some proofs  -/
instance (c : ZKConfig) : NeZero c.k := ⟨by
  intro h_zero
  have h_fits := c.p_fits
  rw [h_zero, Nat.pow_zero] at h_fits
  have h_ge_2 := c.p_prime.two_le
  grind
⟩

/- The finite field F_p induced by the configuration -/
abbrev FF (c : ZKConfig) := ZMod c.p

/- This function should be used to generate an instance of ZKConfig
   at runtime, in case we want to provide external c.p and c.k.

   Warnning: it might be slow to check primality at runtime.
-/
def mkZKConfig (k_input : Nat) (p_input : Nat) : Except String ZKConfig :=
  if h_prime : Nat.Prime p_input then -- Check if p is Prime
    if h_fits : p_input < 2^k_input then -- Check if p fits in k bits
      return {
        k := k_input
        p := p_input
        p_prime := h_prime
        p_fits  := h_fits
      }
    else
      throw s!"Error: {p_input} is too large for {k_input} bits."
  else
    throw s!"Error: {p_input} is not a prime number."


/- A prime number used in the Goldilocks field -/
def goldilocks_p : ℕ := 18446744069414584321 -- 2^64 - 2^32 + 1

/- Use an axiom to provide the proof that goldilocks_p is a prime
   without the kernel "thinking"
-/
axiom goldilocks_is_prime : Nat.Prime goldilocks_p

/- The Goldilocks field configuration -/
def goldilocks64 : ZKConfig := {
  k := 64
  p := goldilocks_p
  p_prime := goldilocks_is_prime
  p_fits := by decide
}

/- We need to add a fact that myConfig.p is a prime so Lean can
   find it automatically.
-/
instance : Fact goldilocks64.p.Prime := ⟨goldilocks64.p_prime⟩ -- ⟨⟩ are for fact


def F11 : ZKConfig := {
  k := 4
  p := 11
  p_prime := by decide
  p_fits := by decide
}

/- We need to add a fact that myConfig.p is a prime so Lean can
   find it automatically.
-/
instance : Fact F11.p.Prime := ⟨F11.p_prime⟩ -- ⟨⟩ are for fact
