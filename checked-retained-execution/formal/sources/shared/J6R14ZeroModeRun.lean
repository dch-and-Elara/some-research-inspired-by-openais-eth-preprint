import J6R12IntegralDirectPrinted
import J6R12RepackRootReady

/-! A prescribed legal outer probe builds the actual source child host with
beta=0. The inner recursion is the certified run on this child itself.
Other modes that its own lower-level algorithm uses are not parent
acquisitions, and are not assumed to vanish. -/
namespace J6R14ZeroMode
open scoped Classical Polynomial BigOperators
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R12Blueprint J6R11Blueprint J6R10Repack J6R11Repack J6R12Repack
open J6R10Integral J6R11Integral J1PPrinted
noncomputable section

variable {f : ℤ[X]} {ell s C : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c) (t : Center (printedParams (f:=f) (ell:=ell) s) c)

def zeroChild (z : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)) (g : Fin 64) : Call (PhysicalHost f ell) :=
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let host := actualPacketHost (packing sel d) (centerIndex d t) (centerNonzero t) rfl
    (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) (box_two_nil (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) f ell) z c.host.file 0 g
  ⟨host,c.depth+1,host.edgeCount,(registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)⟩

theorem zero_legal :
    0 ∈ J6RecursiveMenu.menu (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) (siteWeight sel d t) := by
  rw [J6RecursiveMenu.exact_printed_menu _ _ (siteWeight_pos sel d t)]
  simpa [J6RecursiveMenu.weighted] using J6R12Blueprint.register_positive d t

set_option maxHeartbeats 4300000 in
theorem zeroChild_stable (seed : Stable s C c) (z : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)) (g : Fin 64) :
    Stable s C (zeroChild sel d t z g) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let new := actualPacketHost (packing sel d) (centerIndex d t) (centerNonzero t) rfl
    (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) (box_two_nil (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) f ell) z c.host.file 0 g
  have hP : c.prec ≤ (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) :=
    (child_monotone c.prec _ _ _ t.val (Nat.zero_lt_of_lt d.active)).le
  have hM : 0 < c.host.edgeCount := d.edgeCount.symm ▸ Nat.zero_lt_of_lt d.active
  have hnew := J6R12Repack.generated_invariants (H:=c.host) (packing sel d)
    (centerIndex d t) (centerNonzero t) rfl c.prec (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) (box_two_nil (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) f ell)
    z 0 g (sourceDelta s) (Fintype.card_fin 64) hM d.degree d.packetDegree d.tags hP
  change GoodDegree new (sourceDelta s) ∧ GoodTags new (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) ∧
    32*new.edgeCount ≤ 3*c.host.edgeCount ∧ new.edgeCount < c.host.edgeCount at hnew
  have hcard : 8*new.edgeCount ≤ c.edges := by
    have h := hnew.2.2.1
    rw [d.edgeCount] at h
    omega
  change Stable s C ⟨new,c.depth+1,new.edgeCount,(registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)⟩
  refine ⟨rfl,hnew.1,hnew.2.1,?_⟩
  change 8^(c.depth+1)*new.edgeCount ≤ C*s
  rw [pow_succ,mul_assoc]
  exact (Nat.mul_le_mul_left _ hcard).trans seed.sizeByDepth

def zeroChildRun (hf : f.Monic) (z : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)) (g : Fin 64) : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) :=
  let dest := zeroChild sel d t z g
  (J6R12Blueprint.sourceBlueprint sel dest hf).program.run dest

theorem zeroChildRun_exact (cfg : RootBounds s C f) (seed : Stable s C c)
    (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (z : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)) (g : Fin 64) :
    zeroChildRun sel d t hf z g =
      (letI := c.host.finiteEdge
       letI := c.host.finiteRow
       letI := c.host.finiteCol
       reduce (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) f ell (actualChildTruth (packing sel d) (centerIndex d t)
         (centerNonzero t) rfl (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) z c.host.file hf 0 g)) := by
  let dest := zeroChild sel d t z g
  unfold zeroChildRun
  rw [J6R12Integral.printed_run_exact cfg sel dest (zeroChild_stable sel d t seed z g) hf hF]
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact congrArg (reduce (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) f ell)
    (J6R12Integral.actualPacketHost_truth (packing sel d) (centerIndex d t) (centerNonzero t)
      rfl (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) z c.host.file hf 0 g)

def zeroRuntime (hf : f.Monic) (z : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)) : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) :=
  ∏ g : Fin 64, zeroChildRun sel d t hf z g

#print axioms zeroChild
#print axioms zero_legal
#print axioms zeroChild_stable
#print axioms zeroChildRun
#print axioms zeroChildRun_exact
#print axioms zeroRuntime
end
end J6R14ZeroMode
