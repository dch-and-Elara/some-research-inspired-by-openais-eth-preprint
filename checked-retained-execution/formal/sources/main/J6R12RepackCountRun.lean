import J6R12RepackLiteralRun
import J6R12RepackBoolCount

/-! The actual recursive program agrees with the literal physical gate
count in its source receiving ring, not just an unnamed tensor value. -/
namespace J6R12Repack
open scoped Polynomial
open Polynomial J6Mesh P11FullPacking J6OrientedHost J1PPrinted
open J6ActiveRun J6R9Recursive J6R11Repack J6R12Blueprint

variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

set_option maxHeartbeats 2000000 in
theorem literal_run_gate_count (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree = 4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v ≤ sourceDelta (physicalSize m native))
    (hf : f.Monic) (hF : 0 < f.natDegree)
    (hp : 0 < p) (hℓ : 0 < ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    literalRun (ell:=ell) p m l q native T w mask hm hL hn hf =
      (literalGateCount m l q T w : Box f ell p) := by
  rw [exact_literal_run p m l q native T w mask hm hL hn hfield hsize hdeg hf hF,
    exact_root_integral_gate_count f ell p m l q T w hf hp hF hℓ, map_natCast]

#print axioms literal_run_gate_count
end J6R12Repack
