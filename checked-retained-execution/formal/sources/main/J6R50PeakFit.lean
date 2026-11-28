
import J6R50PeakLocal
import J6R49LiveNativeWidth
import J6R24MeteredRecursionTight

/-! Replace each non-mode slot width by explicit printed guards, while
retaining the current edge scale. The high precision is stated as a
separate hypothesis here; the canonical common field discharges it. -/
namespace J6R50Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits

set_option autoImplicit false
set_option maxRecDepth 3200
set_option maxHeartbeats 16000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def centreCap (s : ℕ) : ℕ := 2^(Nat.clog 2 s+1)

def probeCap (s : ℕ) : ℕ := 2^(4*Nat.clog 2 s)+1

def commonSlope (s : ℕ) : ℕ := 24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)

def numericBase (s C ell e : ℕ) : ℕ :=
  centreCap s * (ell*(e*precisionSize s C))

def numericSlope (s C ell e : ℕ) : ℕ :=
  centreCap s*(ell*(e*commonSlope s))+
    probeCap s*((4*(C*s))*(ell*(e*(siteConstant C*s))))

def HighFit (R : StreamingResident T key prec tw bw page q) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : J6R32StatefulArithmetic.Path sel r x) (a : (S).cutoff<x.edges),
    x.prec+(R.active p a).extraPrecision ≤ precisionSize s C+x.edges*commonSlope s

theorem observed_prefix_dimensions
    {R : StreamingResident T key prec tw bw page q} {p : J6R32StatefulArithmetic.Path sel r c} {w : (Plan sel).Slot c}
    (E : NumericAt R p w) :
    E.before.length≤centreCap s ∧ w.val.2.1.val+2≤probeCap s ∧
      ((R.active p w.property).tape w.val.1).window≤4*(C*s) := by
  classical
  let D := R.active p w.property
  have hpre : E.before.length≤D.centres.length := by
    rw [E.split,List.length_append,List.length_cons]
    omega
  have hlen := full_roster_length D.centres D.centreUnique D.centreComplete
  have hctr : Nat.card (Center S c)≤centreCap s :=
    (centers_le S c).trans (Nat.pow_le_pow_right (by decide)
      (Nat.succ_le_succ (bits_le_lam (Nat.clog 2 s) c.depth)))
  let d := ready_reachable cfg sel p.reached T.rootStable w.property
  have hfit := d.fit
  change J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth)≤2^f.natDegree at hfit
  rw [cfg.coefficient] at hfit
  have hz := w.val.2.1.isLt
  change w.val.2.1.val<J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth) at hz
  have hProbe : w.val.2.1.val+2≤probeCap s := by unfold probeCap; omega
  obtain ⟨hu,huM⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached w.property
  have he := (stable_reachable cfg sel p.reached T.rootStable).sizeByDepth
  have hm : c.edges≤C*s :=
    (Nat.le_mul_of_pos_left _ (by positivity : 0<(8:ℕ)^c.depth)).trans he
  have hw := order_bound c.edges ((S).levelWidth c.depth) w.val.1.val hu huM
  exact ⟨hpre.trans (hlen.le.trans hctr),hProbe,hw.trans (Nat.mul_le_mul_left 4 hm)⟩

theorem actual_numeric_fields_affine
    {R : StreamingResident T key prec tw bw page q} {p : J6R32StatefulArithmetic.Path sel r c} {w : (Plan sel).Slot c}
    (E : NumericAt R p w) (retire : J→ℕ) (initial : L)
    (depth : r.depth=0) (rootPrec : r.prec≤C*s) (high : HighFit R) :
    (E.payload retire initial).length≤numericBase s C ell f.natDegree+
      c.edges*numericSlope s C ell f.natDegree := by
  let D := R.active p w.property
  let t := w.val.1
  let z := w.val.2.1
  obtain ⟨hCtr,hProbe,hOrd⟩ := observed_prefix_dimensions E
  have hHigh := high p w.property
  have hLow := register_bits_by_current_edges cfg sel p.reached T.rootStable depth rootPrec w.property t
  have h1 :
      E.before.length*(ell*(f.natDegree*(c.prec+D.extraPrecision)))≤
        centreCap s*(ell*(f.natDegree*(precisionSize s C+c.edges*commonSlope s))) :=
    Nat.mul_le_mul hCtr (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hHigh))
  have h2 :
      (z.val+2)*((D.tape t).window*(ell*(f.natDegree*registerPrecision S c t)))≤
        probeCap s*((4*(C*s))*(ell*(f.natDegree*(siteConstant C*c.edges*s)))) :=
    Nat.mul_le_mul hProbe (Nat.mul_le_mul hOrd (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hLow)))
  rw [actual_numeric_payload_at_address E retire initial]
  exact (Nat.add_le_add h1 h2).trans_eq (by unfold numericBase numericSlope; ring)

#print axioms observed_prefix_dimensions
#print axioms actual_numeric_fields_affine
end J6R50Peak
