import J6R10ReachableSchedule
import J1PPrintedSize
import J1PPrintedMesh
import J6R9RecursiveProbes

/-! Actual printed depth-dependent schedule on genuine reachable calls.
The independent root size and parameter thresholds are explicit.
No feasibility axiom quantifies over arbitrary calls with oversized
edge populations. -/
namespace J6R10Reachable
open J6ActiveRun J6ActiveSchedule J6R9Recursive J1PPrinted
open scoped Polynomial

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

def printedShape (s : ℕ) (W : Call Host → ℤ → Mode → ℕ) : Shape Host Mode where
  cutoff := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
  levelWidth := stepU (Nat.clog 2 s)
  levelBits := stepA (Nat.clog 2 s)
  weight := W

variable {Value : ℕ → Type*}
variable {s : ℕ} {W : Call Host → ℤ → Mode → ℕ}
variable {P : Program (printedShape s W) Value} {root c : Call Host}

theorem printed_taper_reachable (h : Reach P root c) (rootDepth : root.depth = 0) (C : ℕ)
    (seed : root.edges ≤ C*s) (hC : 0 < C)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (hsize : (2*epsDen)^30*C^10 ≤ Nat.clog 2 s)
    (hactive : (printedShape s W).cutoff < c.edges) :
    1 ≤ (printedShape s W).levelWidth c.depth ∧
    (printedShape s W).levelWidth c.depth ≤ (printedShape s W).levelBits c.depth ∧
    (printedShape s W).levelWidth c.depth ≤ c.edges :=
  printed_taper_legal s c.edges C c.depth hU hC hsize hactive
    (source_root_edge_bound P h rootDepth C s seed)

theorem printed_depth_reachable (h : Reach P root c) (rootDepth : root.depth = 0) (C : ℕ)
    (seed : root.edges ≤ C*s) (hLambda : 0 < Nat.clog 2 s)
    (hactive : (printedShape s W).cutoff < c.edges) :
    ((2:ℕ)^c.depth)^6 ≤ C^2*Nat.clog 2 s :=
  depth_sixth_bound s c.edges C c.depth hLambda hactive (source_root_edge_bound P h rootDepth C s seed)

omit [Fintype Mode] [DecidableEq Mode] in
theorem printed_pack_reachable (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (hactive : (printedShape s W).cutoff < c.edges) :
    let L := 2^(printedShape s W).levelBits c.depth
    let D := stepD (Nat.clog 2 s) c.depth
    2*D^2*sourceDelta s ≤ c.edges ∧ L*D ≤ c.edges ∧ 2*L ≤ sourceDelta s :=
  source_packing_conditions s c.edges c.depth hU hactive

set_option exponentiation.threshold 12000 in
theorem printed_probe_fit_reachable (h : Reach P root c) (rootDepth : root.depth = 0) (C : ℕ)
    (seed : root.edges ≤ C*s) (hC : C ≤ s)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (hactive : (printedShape s W).cutoff < c.edges) (f : ℤ[X])
    (hf : f.natDegree = 4*Nat.clog 2 s) : ProofFit (printedShape s W) f c := by
  let lam := Nat.clog 2 s
  let L := stepL lam c.depth
  have hL4 : 4 ≤ L := stepL_ge_four lam c.depth hU
  have hL3 : L^3 < s := by
    exact (Nat.pow_le_pow_right (show 0<L by omega) (show (3:ℕ) ≤ 1000 by decide)).trans_lt
      (dimensions_small s c.depth hU).1
  have h2L : 2*L ≤ s := by
    have hs : 2 ≤ L^2 := by
      calc
        2 ≤ L := by omega
        _ ≤ L*L := by simpa using Nat.mul_le_mul_left L (show 1≤L by omega)
        _ = L^2 := (pow_two L).symm
    exact ((Nat.mul_le_mul_right L hs).trans_eq (Nat.pow_succ L 2).symm).trans hL3.le
  have hM : c.edges ≤ s^2 := by
    have hseed := source_root_edge_bound P h rootDepth C s seed
    have hm : c.edges ≤ (8:ℕ)^c.depth*c.edges :=
      Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
    exact (hm.trans hseed).trans (by simpa only [pow_two] using Nat.mul_le_mul_right s hC)
  have hp : 1 ≤ c.edges := Nat.zero_lt_of_lt hactive
  have hdl : J9PrintedSchedule.probeCount c.edges L ≤ c.edges*(2*L) := by
    unfold J9PrintedSchedule.probeCount J9PrintedSchedule.degreeBound
    calc
      _ ≤ c.edges*(2*L-1)+c.edges := Nat.add_le_add_left hp _
      _ = c.edges*((2*L-1)+1) := by ring
      _ = _ := by congr 1; omega
  have hD : J9PrintedSchedule.probeCount c.edges L ≤ s^4 := by
    apply hdl.trans
    calc
      _ ≤ s^2*s := Nat.mul_le_mul hM h2L
      _ = s^3 := (pow_succ s 2).symm
      _ ≤ s^4 := Nat.pow_le_pow_right (show 0<s by omega) (by decide)
  change J9PrintedSchedule.probeCount c.edges L ≤ 2^f.natDegree
  rw [hf]
  exact NativeProbeRing.printed_fit s lam _ (Nat.le_pow_clog (by decide) s) hD

#print axioms printed_taper_reachable
#print axioms printed_depth_reachable
#print axioms printed_pack_reachable
#print axioms printed_probe_fit_reachable
end J6R10Reachable