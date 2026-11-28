
import J6R50PeakCanonical
import J6R50PeakStrip

/-! The running active frame can be observed during its own final
strip after descendants have closed. Add one actual local scratch
snapshot, not a fictitious copy at every suspended ancestor. -/
namespace J6R50Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 17000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def stripRoof (s C ell e : ℕ) : ℕ :=
  (2*ell*e+e+2)*(precisionSize s C+(C*s)*commonSlope s)

variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem current_strip_uniform_selected_cap (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (origin : R.rootLive initial)
    (legal : ReadyOnStack R.births initial) (p : Path sel r c) (a : (S).cutoff<c.edges)
    (i : Fin ell) (j : Fin ((R.active p a).high (reachable_positive T p.reached)).words.length)
    (high : HighFit R) :
    (currentStripFields R retire initial p a i j).length≤stripRoof s C ell f.natDegree := by
  let Q := c.prec+(R.active p a).extraPrecision
  let W := precisionSize s C+(C*s)*commonSlope s
  have hM : c.edges≤C*s := (Nat.le_mul_of_pos_left _ (by positivity : 0<(8:ℕ)^c.depth)).trans
    (stable_reachable cfg sel p.reached T.rootStable).sizeByDepth
  have hQ : Q≤W := (high p a).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hM) _)
  have hP : c.prec≤W := (Nat.le_add_right _ _).trans hQ
  have hBound := same_run_strip_fields_cap R retire initial origin legal p a i j
  refine hBound.trans ?_
  calc
    _ ≤ ell*(f.natDegree*W)+ell*(f.natDegree*W)+f.natDegree*W+2*W :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hQ))
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hP)))
          (Nat.mul_le_mul_left _ hP))
        (Nat.mul_le_mul_left _ hQ)
    _=stripRoof s C ell f.natDegree := by unfold W stripRoof; ring

theorem canonical_current_strip_and_ancestral_peak (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (origin : R.rootLive initial)
    (legal : ReadyOnStack R.births initial)
    (d₀ : r.depth=0) (p₀ : r.prec≤C*s) (qFit : q≤uniformWidth s C)
    (pageBound : ℕ) (rows : AllExactPages R.births)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (i : Fin ell)
    (j : Fin (((canonicalStreaming R).active p a).high (reachable_positive T p.reached)).words.length) :
    ∃ m n,JointSuspensions (canonicalStreaming R) retire initial p m n ∧
      residentAtlasBits (stackBank R.births initial p)+m+n+
        (currentStripFields (canonicalStreaming R) retire initial p a i j).length≤
          selectedRoof (s:=s) (C:=C) initial r.edges pageBound+stripRoof s C ell f.natDegree := by
  obtain ⟨m,n,trace,h⟩ := canonical_exact_payload_any_source_path R retire initial d₀ p₀ qFit pageBound rows bits p
  exact ⟨m,n,trace,Nat.add_le_add h
    (current_strip_uniform_selected_cap (canonicalStreaming R) retire initial origin legal p a i j
      (actual_canonical_high_fits R d₀ p₀))⟩

#print axioms current_strip_uniform_selected_cap
#print axioms canonical_current_strip_and_ancestral_peak
end J6R50Peak
