
import J6R50PeakStartPrecision
import J6R50PeakFit
import J6R49LiveCanonicalRun

/-! Actual local selected fields have a uniform polynomial-form bound
at arbitrary absolute starting depth and real inherited precision.
The typed cursor still has its original checked width guard. -/
namespace J6R50Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits

set_option autoImplicit false
set_option maxRecDepth 3400
set_option maxHeartbeats 17000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def absoluteModeCap (s C ell e P : ℕ) : ℕ :=
  frameBase (uniformWidth s C) (6*(C*s)*P)+2*ell*(e*P)

def absoluteHighCap (s C P : ℕ) : ℕ := P+(C*s)*commonSlope s

def absoluteNumericCap (s C ell e P : ℕ) : ℕ :=
  centreCap s*(ell*(e*absoluteHighCap s C P)) + probeCap s*((4*(C*s))*(ell*(e*P)))

theorem actual_edges_uniform (T : Prepared cfg sel r hf) (p : J6R32StatefulArithmetic.Path sel r c) :
    c.edges≤C*s :=
  (Nat.le_mul_of_pos_left _ (by positivity : 0<(8:ℕ)^c.depth)).trans
    (stable_reachable cfg sel p.reached T.rootStable).sizeByDepth

theorem canonical_absolute_word_width (R : StreamingResident T key prec tw bw page q)
    (p : J6R32StatefulArithmetic.Path sel r c) (a : (S).cutoff<c.edges) :
    c.prec+((canonicalStreaming R).active p a).extraPrecision≤
      absoluteHighCap s C (absolutePrecision s r.edges r.prec) := by
  have hp := absolute_inherited_precision_cap cfg sel T.rootStable p
  have hm := actual_edges_uniform T p
  obtain ⟨hu,huM⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached a
  have ha : (S).levelBits c.depth≤Nat.clog 2 s := bits_le_lam _ _
  have loss := simple_common_scale_cap ha hu huM
  exact Nat.add_le_add hp (loss.trans (Nat.mul_le_mul_right (commonSlope s) hm))

theorem mode_selected_payload_absolute (T : Prepared cfg sel r hf) (p : J6R32StatefulArithmetic.Path sel r c)
    (o : NativeSuspension (C:=C) (sel:=sel) c) :
    o.measure.bits≤absoluteModeCap s C ell f.natDegree (absolutePrecision s r.edges r.prec) := by
  let P := absolutePrecision s r.edges r.prec
  have hP := absolute_register_precision_cap cfg sel T.rootStable p o.ready.active o.center
  have hM := actual_edges_uniform T p
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have hE : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact o.ready.edgeCount
  have shape := physical_roster_length (packing sel o.ready) (centerIndex o.ready o.center)
    o.input.modes o.input.nodup o.input.allModes
  rw [hE] at shape
  have e := congrArg List.length o.input.weightMeaning
  simp only [List.length_map] at e
  have hn : o.input.words.length≤6*(C*s)*P := by
    rw [e]
    exact shape.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hP)
  have cap := actual_event_buffers_fit o.state o.stateFit o.outer o.inner
  change o.measure.bits≤_ at cap
  rw [o.frame.natDegree hf] at cap
  have prefixSquares : (o.input.words.length+2)^2≤(6*(C*s)*P+2)^2 := by
    gcongr
  unfold absoluteModeCap frameBase
  exact cap.trans
    (Nat.add_le_add
      (Nat.mul_le_mul (Nat.add_le_add (Nat.mul_le_mul_left 2 prefixSquares) hn)
        (Nat.add_le_add_right o.fitsWord 1))
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hP)))

theorem numeric_selected_payload_absolute
    {R : StreamingResident T key prec tw bw page q} {p : J6R32StatefulArithmetic.Path sel r c} {w : (Plan sel).Slot c}
    (E : NumericAt (canonicalStreaming R) p w) (retire : J→ℕ) (initial : L) :
    (E.payload retire initial).length≤absoluteNumericCap s C ell f.natDegree
      (absolutePrecision s r.edges r.prec) := by
  obtain ⟨hCtr,hProbe,hOrd⟩ := observed_prefix_dimensions E
  have hi := canonical_absolute_word_width R p w.property
  have lo := absolute_register_precision_cap cfg sel T.rootStable p w.property w.val.1
  rw [actual_numeric_payload_at_address E retire initial]
  unfold absoluteNumericCap
  exact Nat.add_le_add
    (Nat.mul_le_mul hCtr (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hi)))
    (Nat.mul_le_mul hProbe (Nat.mul_le_mul hOrd (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ lo))))

#print axioms actual_edges_uniform
#print axioms canonical_absolute_word_width
#print axioms mode_selected_payload_absolute
#print axioms numeric_selected_payload_absolute
end J6R50Peak
