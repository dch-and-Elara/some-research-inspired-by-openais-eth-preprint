import J6R12RepackCountRun
import J6R12RepackReadNatural

/-! Exact integer readout of the literal source recursion, when its
base precision is chosen to contain the whole physical gate count.
This simple sufficient inequality does not claim optimal source
precision or an unverified bit-complexity bound. -/
namespace J6R12Repack
open scoped Polynomial
open Polynomial J6Mesh P11FullPacking J6OrientedHost J1PPrinted
open J6ActiveRun J6R9Recursive J6R11Repack J6R12Blueprint

variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

set_option maxHeartbeats 2200000 in
theorem literal_run_natural_count (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree = 4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v ≤ sourceDelta (physicalSize m native))
    (hf : f.Monic) (hF : 0 < f.natDegree)
    (hℓ : 0 < ell) (hbits : M m < p)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    boxNatural f ell p hf (literalRun p m l q native T w mask hm hL hn hf) =
      literalGateCount m l q T w := by
  have hp := Nat.zero_lt_of_lt hbits
  rw [literal_run_gate_count p m l q native T w mask hm hL hn hfield hsize hdeg hf hF hp hℓ]
  exact boxNatural_of_nat f ell p hf hp hℓ hF _ <|
    (literal_gate_count_bound m l q T w hm hL (Fintype.card_fin 64)).trans_lt
      (Nat.pow_lt_pow_right (by decide) hbits)

#print axioms literal_run_natural_count
end J6R12Repack
