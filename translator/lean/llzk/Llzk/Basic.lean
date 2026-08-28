import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Llzk.Primes

/- Configuration for ZK environment: the prime, number of bits, and
   some corresponding requirements

   Numbers are supposed to be signed, with the following ordering:

      Negative         Positive
   ---------------- ------------------
   midpoint,...,p-1,0,1,...,midpoint-1

-/
structure ZKConfig where
  k : ℕ  -- bit-width of p
  p : ℕ  -- the prime number
  midpoint : ℕ := p / 2 + 1 -- the midpoint of the field, used for signed representation
  p_prime : p.Prime -- stating that p is a prime.
  p_fits : p ≥ 2^(k-1) && p < 2^k -- k is indeed the bit-width of p
  midpoint_ok : midpoint = p / 2 + 1 := by rfl -- ensure midpoint is correctly defined

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

/- toString of FF values -/
instance {c : ZKConfig} : ToString (FF c) where
  toString x := s!"{x.val}"

/- This function should be used to generate an instance of ZKConfig
   at runtime, in case we want to provide external c.p and c.k.

   Warning: it might be slow at runtime.
-/
def mkZKConfig (k_input : Nat) (p_input : Nat) : Except String ZKConfig :=
  if h_prime : Nat.Prime p_input then -- Check if p is Prime
    if h_fits : p_input ≥ 2^(k_input-1) && p_input < 2^k_input then -- Check if p fits in k bits
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


/- The Goldilocks field configuration.

   We need to add a fact that goldilocks.p is a prime so Lean can
   find it automatically.
-/
def goldilocks : ZKConfig := {
  k := 64
  p := goldilocks_p
  p_prime := goldilocks_is_prime
  p_fits := by rfl
}

instance : Fact goldilocks.p.Prime := ⟨goldilocks.p_prime⟩


/- The secp256r1 field configuration.

   We need to add a fact that secp256r1.p is a prime so Lean can
   find it automatically.
-/

def secp256r1 : ZKConfig := {
  k := 256
  p := secp256r1_p
  p_prime := secp256r1_is_prime
  p_fits := by rfl
}

instance : Fact secp256r1.p.Prime := ⟨secp256r1.p_prime⟩


/- The Pallas field configuration.

   We need to add a fact that pallas.p is a prime so Lean can
   find it automatically.
-/
def pallas : ZKConfig := {
  k := 255
  p := pallas_p
  p_prime := pallas_is_prime
  p_fits := by rfl
}
instance : Fact pallas.p.Prime := ⟨pallas.p_prime⟩


/- The Vesta field configuration.

   We need to add a fact that vesta.p is a prime so Lean can
   find it automatically.
-/

def vesta : ZKConfig := {
  k := 255
  p := vesta_p
  p_prime := vesta_is_prime
  p_fits := by rfl
}

instance : Fact vesta.p.Prime := ⟨vesta.p_prime⟩


def bn128 : ZKConfig := {
  k := 254
  p := bn128_p
  p_prime := bn128_is_prime
  p_fits := by rfl
}

instance : Fact bn128.p.Prime := ⟨bn128.p_prime⟩


def grumpkin : ZKConfig := {
  k := 254
  p := grumpkin_p
  p_prime := grumpkin_is_prime
  p_fits := by rfl
}

instance : Fact grumpkin.p.Prime := ⟨grumpkin.p_prime⟩

def bls12377 : ZKConfig := {
  k := 254
  p := bls12377_p
  p_prime := bls12377_is_prime
  p_fits := by rfl
}
instance : Fact bls12377.p.Prime := ⟨bls12377.p_prime⟩

def bls12381 : ZKConfig := {
  k := 255
  p := bls12381_p
  p_prime := bls12381_is_prime
  p_fits := by rfl
}
instance : Fact bls12381.p.Prime := ⟨bls12381.p_prime⟩




/- The following are "toy" fields, just for debugging as their encoding is small. -/


def F11 : ZKConfig := {
  k := 4
  p := 11
  p_prime := by decide
  p_fits := by rfl
}

instance : Fact F11.p.Prime := ⟨F11.p_prime⟩


def F7 : ZKConfig := {
  k := 3
  p := 7
  p_prime := by decide
  p_fits := by rfl
}

instance : Fact F7.p.Prime := ⟨F7.p_prime⟩
