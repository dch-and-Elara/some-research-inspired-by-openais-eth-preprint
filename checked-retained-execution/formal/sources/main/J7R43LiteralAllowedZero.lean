import J7R43LiteralRun
import J7R43LiteralProbe

/-! The paper's allowed zero probe gives a genuine Appendix-D physical
child even when this separately fixed implementation prefix omits zero.
Only that first sample is chosen: actual descendant recursion, layout
selector, creation precision, and native evaluator remain unchanged. -/
namespace J7R43Literal
open scoped Polynomial BigOperators Classical
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R12Blueprint J6R11Blueprint J6R12Integral J6R11Integral
open J1PPrinted J6R10Repack J6R10Integral J6R14SpecializedBox
open J6R12Repack J6R11Repack
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell : ℕ} {s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)
variable (β : LiteralMenu sel d t) (g : Fin 64)

def allowedZeroHost : PhysicalHost f ell := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
  exact actualPacketHost (packing sel d) (centerIndex d t)
    (centerNonzero t) rfl p (box_two_nil p f ell) 0 c.host.file β.val g

def allowedZeroCall : Call (PhysicalHost f ell) :=
  let new := allowedZeroHost (s:=s) (c:=c) sel d t β g
  ⟨new,c.depth+1,new.edgeCount,registerPrecision (printedParams (f:=f) (ell:=ell) s) c t⟩

set_option maxHeartbeats 5000000 in
theorem allowed_zero_call_stable (hc : Stable s C c) :
    Stable s C (allowedZeroCall (s:=s) (c:=c) sel d t β g) := by
  let S := printedParams (f:=f) (ell:=ell) s
  let p := registerPrecision S c t
  let i := centerIndex d t
  let new := allowedZeroHost (s:=s) (c:=c) sel d t β g
  have hincrease : c.prec ≤ p :=
    (child_monotone c.prec _ _ _ t.val (Nat.zero_lt_of_lt d.active)).le
  have hM : 0 < c.host.edgeCount := d.edgeCount.symm ▸ Nat.zero_lt_of_lt d.active
  have hnew := generated_invariants (H:=c.host) (packing sel d) i (centerNonzero t) rfl c.prec p
    (box_two_nil p f ell) (0:Box f ell p) β.val g
    (sourceDelta s) (Fintype.card_fin 64) hM d.degree d.packetDegree d.tags hincrease
  change GoodDegree new (sourceDelta s) ∧ GoodTags new p ∧
    32*new.edgeCount ≤ 3*c.host.edgeCount ∧ new.edgeCount < c.host.edgeCount at hnew
  have hcard : 8*new.edgeCount ≤ c.edges := by
    have hb := hnew.2.2.1
    rw [d.edgeCount] at hb
    omega
  refine ⟨rfl,hnew.1,hnew.2.1,?_⟩
  change 8^(c.depth+1)*new.edgeCount ≤ C*s
  rw [pow_succ,mul_assoc]
  exact (Nat.mul_le_mul_left _ hcard).trans hc.sizeByDepth

def allowedZeroValue (hf : f.Monic) :
    Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) :=
  let new := allowedZeroCall (s:=s) (c:=c) sel d t β g
  (sourceBlueprint sel new hf).program.run new

set_option maxHeartbeats 4500000 in
include cfg in
theorem allowed_zero_actual_run (hc : Stable s C c) (hf : f.Monic) (hF : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    allowedZeroValue (s:=s) (c:=c) sel d t β g hf =
      (letI := c.host.finiteEdge
       letI := c.host.finiteRow
       letI := c.host.finiteCol
       reduce (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) f ell
        (actualChildTruth (packing sel d) (centerIndex d t) (centerNonzero t) rfl
          (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)
          0 c.host.file hf β.val g)) := by
  let S := printedParams (f:=f) (ell:=ell) s
  let p := registerPrecision S c t
  let next := allowedZeroCall (s:=s) (c:=c) sel d t β g
  have h := printed_run_exact cfg sel next (allowed_zero_call_stable sel d t β g hc) hf hF
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact h.trans (congrArg (reduce p f ell) (actualPacketHost_truth
    (packing sel d) (centerIndex d t) (centerNonzero t) rfl p 0 c.host.file hf β.val g))

set_option maxHeartbeats 3000000 in
theorem allowed_zero_call_matches_fixed
    (z : Probe (printedParams (f:=f) (ell:=ell) s) c)
    (hz : sampleNode (printedParams (f:=f) (ell:=ell) s) f ell c d.fit t z=0) :
    samePacketCall (s:=s) (c:=c) sel d t z β g = allowedZeroCall (s:=s) (c:=c) sel d t β g := by
  unfold samePacketCall allowedZeroCall packetOfSite allowedZeroHost
  dsimp only
  rw [hz]

#print axioms allowedZeroHost
#print axioms allowedZeroCall
#print axioms allowed_zero_call_stable
#print axioms allowed_zero_actual_run
#print axioms allowed_zero_call_matches_fixed
end
end J7R43Literal