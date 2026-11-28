import J6R12IntegralDirectPrinted
import J9R15FrozenErasurePhysical

/-! For a legal printed address the packet child is actually run: the
root's exact dependent menu gives an address witnessing reachability,
and the inherited shrink/degree/creation invariants justify recursion.
The output is the exact projected child tensor at its own ring,
without a free group-value callback. -/
namespace J6R14SpecializedBox
open scoped Polynomial Classical BigOperators
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R12Blueprint J6R11Blueprint
open J1PPrinted J6R12Integral J6R11Integral J9R15FrozenErasurePhysical
noncomputable section
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell : ℕ} {s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c) (t : Center (printedParams (f:=f) (ell:=ell) s) c) (z : Probe (printedParams (f:=f) (ell:=ell) s) c)
variable (β : LiteralMenu sel d t) (g : Fin 64)

def samePacketCall : Call (PhysicalHost f ell) :=
  let host := packetOfSite sel d t z β.val g
  ⟨host,c.depth+1,host.edgeCount,registerPrecision (printedParams (f:=f) (ell:=ell) s) c t⟩

theorem samePacketCall_actual_address :
    ∃ w : NativeAddress (shape (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) sel) c,
      (nativePlan (shape (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) sel) (children (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) sel)).child c ⟨w,d.active⟩ =
        samePacketCall (s:=s) (c:=c) sel d t z β g := by
  let β' := (siteMenuEquiv sel d t).symm β
  refine ⟨⟨t,z,β',g⟩,?_⟩
  rw [child_exact sel d]
  have eq : siteTuple sel d ⟨t,z,β',g⟩ = β.val := by
    rw [← siteMenuEquiv_tuple sel d t z β' g]
    exact congrArg Subtype.val ((siteMenuEquiv sel d t).apply_symm_apply β)
  rw [eq]
  rfl

include cfg in
theorem samePacketCall_stable (seed : Stable s C c) :
    Stable s C (samePacketCall (s:=s) (c:=c) sel d t z β g) := by
  obtain ⟨w,h⟩ := samePacketCall_actual_address sel d t z β g
  rw [← h]
  exact stable_step cfg sel seed ⟨w,d.active⟩

set_option maxHeartbeats 4000000 in
include cfg in
theorem recursively_evaluated_fixed_actual_product
    (seed : Stable s C c) (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    (∏ g : Fin 64,
      (sourceBlueprint sel (samePacketCall (s:=s) (c:=c) sel d t z β g) hf).program.run
        (samePacketCall (s:=s) (c:=c) sel d t z β g)) =
      (letI := c.host.finiteEdge
       letI := c.host.finiteRow
       letI := c.host.finiteCol
       actualProjection (packing sel d) (centerIndex d t) (centerNonzero t) rfl
         (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) (sampleNode (printedParams (f:=f) (ell:=ell) s) f ell c d.fit t z) c.host.file hf β.val) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  unfold actualProjection
  refine Finset.prod_congr rfl ?_
  intro g _
  rw [printed_run_exact cfg sel _ (samePacketCall_stable cfg sel d t z β g seed) hf hF]
  exact congrArg _ (packetOfSite_truth sel d t z β.val g hf)

#print axioms samePacketCall_actual_address
#print axioms samePacketCall_stable
#print axioms recursively_evaluated_fixed_actual_product
end
end J6R14SpecializedBox