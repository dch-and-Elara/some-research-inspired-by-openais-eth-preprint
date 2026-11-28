import J6R12RepackRootStable
import J6R12IntegralDirectPrinted

/-! Thin specialization of the physical recursive source proof to the
very same literal J6 planted input and printed root parameters. -/
namespace J6R12Repack
open scoped Polynomial
open Polynomial J6Mesh P11FullPacking J6OrientedHost J1PPrinted
open J6ActiveRun J6R9Recursive J6R11Repack J6R12Blueprint J6R12Integral

variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

noncomputable def literalRun (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m) (hf : f.Monic) :
    Box f ell p := by
  classical
  let r := physicalRootCall f ell p m l q T w
  let sel := exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
  exact (J6R12Blueprint.sourceBlueprint sel r hf).program.run r

set_option maxHeartbeats 2200000 in
theorem exact_literal_run (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree = 4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v ≤ sourceDelta (physicalSize m native))
    (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    literalRun (ell:=ell) p m l q native T w mask hm hL hn hf =
      reduce p f ell ((physicalRootCall f ell p m l q T w).host.contract hf) := by
  classical
  let r := physicalRootCall f ell p m l q T w
  let sel := exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
  have cfg := exact_j6_root_bounds (f:=f) m native hfield hsize
  have hs := exact_j6_root_stable (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg
  exact printed_run_exact cfg sel r hs hf hF

#print axioms literalRun
#print axioms exact_literal_run
end J6R12Repack
