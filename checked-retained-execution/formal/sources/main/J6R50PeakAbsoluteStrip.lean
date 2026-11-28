
import J6R50PeakAbsolute
import J6R50PeakStrip

/-! One current active strip may be added to the selected absolute-start
ancestry budget.  The extra term is not charged at every ancestor. -/
namespace J6R50Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 17500000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def absoluteStripCap (s C ell e P : ℕ) : ℕ := (2*ell*e+e+2)*absoluteHighCap s C P

variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_absolute_strip_fields (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (origin : R.rootLive initial)
    (legal : ReadyOnStack R.births initial) (p : Path sel r c) (a : (S).cutoff<c.edges)
    (i : Fin ell)
    (j : Fin (((canonicalStreaming R).active p a).high (reachable_positive T p.reached)).words.length) :
    (currentStripFields (canonicalStreaming R) retire initial p a i j).length≤
      absoluteStripCap s C ell f.natDegree (absolutePrecision s r.edges r.prec) := by
  let W := absoluteHighCap s C (absolutePrecision s r.edges r.prec)
  have hi := canonical_absolute_word_width R p a
  have low := absolute_inherited_precision_cap cfg sel T.rootStable p
  have hlo : c.prec≤W := low.trans (Nat.le_add_right _ _)
  have cap := same_run_strip_fields_cap (canonicalStreaming R) retire initial origin legal p a i j
  refine cap.trans ?_
  calc
    _≤ell*(f.natDegree*W)+ell*(f.natDegree*W)+f.natDegree*W+2*W :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hi))
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlo)))
          (Nat.mul_le_mul_left _ hlo))
        (Nat.mul_le_mul_left _ hi)
    _=_ := by unfold absoluteStripCap W; ring

theorem arbitrary_start_current_strip_and_ancestry_peak
    (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (origin : R.rootLive initial)
    (legal : ReadyOnStack R.births initial)
    (qFit : q≤uniformWidth s C) (pageBound : ℕ) (rows : AllExactPages R.births)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound)
    (p : Path sel r c) (a : (S).cutoff<c.edges) (i : Fin ell)
    (j : Fin (((canonicalStreaming R).active p a).high (reachable_positive T p.reached)).words.length) :
    ∃ m n,JointSuspensions (canonicalStreaming R) retire initial p m n ∧
      residentAtlasBits (stackBank R.births initial p)+m+n+
        (currentStripFields (canonicalStreaming R) retire initial p a i j).length≤
          absoluteSelectedRoof (s:=s) (C:=C) initial r.edges r.prec pageBound+
            absoluteStripCap s C ell f.natDegree (absolutePrecision s r.edges r.prec) := by
  obtain ⟨m,n,h,b⟩ := actual_absolute_path_selected_peak R retire initial qFit pageBound rows bits p
  exact ⟨m,n,h,Nat.add_le_add b (actual_absolute_strip_fields R retire initial origin legal p a i j)⟩

#print axioms actual_absolute_strip_fields
#print axioms arbitrary_start_current_strip_and_ancestry_peak
end J6R50Peak
