
import A2R45LiteralAllModesRecover
import J6R12IntegralDirectPrinted
import J6DeformationPoly

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5300000
set_option maxRecDepth 2050
set_option linter.unusedSectionVars false

/-! Feed the actual parent's completed sum over its exact native mode
menu to the original source recovery. The oracle interface contains
one response per centre/probe, not a factored or fine-mode bank. -/
namespace A2R45Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R12Blueprint
open J6R11Blueprint J6R12Integral J1PPrinted J6R10Reachable

noncomputable section
variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable (sel : Selector S Δ) {c : Call (PhysicalHost f ell)} (d : Ready S Δ c)

def actualWhole (hf : f.Monic) : WholeAnswers S f ell c := fun t z =>
  ∑ β : LiteralMenu sel d t, ∏ g : Fin 64,
    reduce (registerPrecision S c t) f ell ((packetOfSite sel d t z β.val g).contract hf)

theorem wholeSample_is_original_evaluation (hf : f.Monic) (t : Center S c) (z : Probe S c) :
    actualWhole sel d hf t z =
      ((actualJet sel d hf t.val).map (reduce (registerPrecision S c t) f ell)).eval
        (sampleNode S f ell c d.fit t z) :=
  (native_parent_probe sel d t z hf).symm

theorem exact_aggregate_client (hf : f.Monic) (hF : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hu : 0<S.levelWidth c.depth) (huM : S.levelWidth c.depth≤c.edges)
    (oracle : WholeAnswers S f ell c)
    (correct : ∀ t z,oracle t z=actualWhole sel d hf t z) :
    wholeAssemble S f ell c d.fit oracle=reduce c.prec f ell (c.host.contract hf) := by
  refine wholeAssemble_exact S f hf hF ell c d.fit hu huM
    (actualF sel d hf) (actualF_degree sel d hf) (actualJet sel d hf)
    (fun t ht=>actualJet_local sel d hf ⟨t,ht⟩) (c.host.contract hf)
    (actualF_origin sel d hf) oracle ?_
  intro t z
  exact (correct t z).trans (wholeSample_is_original_evaluation sel d hf t z)

include d in
theorem whole_address_count :
    Fintype.card (Center S c×Probe S c)≤2*c.edges*(2*c.edges^2+1) := by
  let a := S.levelBits c.depth
  let u := S.levelWidth c.depth
  let L : ℕ := 2^a
  let D := J9PrintedSchedule.arrayCard a
  have hd : 1≤D := Nat.succ_le_of_lt (by unfold D J9PrintedSchedule.arrayCard; positivity)
  have hL : L≤c.edges := by
    have h : L≤L*D := by simpa only [mul_one] using Nat.mul_le_mul_left L hd
    exact h.trans d.paddedSlots
  have centers : Fintype.card (Center S c)≤2*c.edges := by
    have hs : (active a c.edges u).card≤(P1DyadicGrid.grid a).card :=
      Finset.card_le_card (fun _ ht=>(active_grid a c.edges u ht).1)
    rw [J6DeformationPoly.grid_card] at hs
    change (active a c.edges u).attach.card≤2*c.edges
    rw [Finset.card_attach]
    exact hs.trans (Nat.mul_le_mul_left 2 hL)
  have probes : Fintype.card (Probe S c)≤2*c.edges^2+1 := by
    rw [Fintype.card_fin]
    change c.edges*(2*L-1)+1≤2*c.edges^2+1
    have h := Nat.mul_le_mul_left c.edges ((Nat.sub_le (2*L) 1).trans (Nat.mul_le_mul_left 2 hL))
    calc
      _ ≤ c.edges*(2*c.edges)+1 := Nat.add_le_add_right h 1
      _ = _ := by ring
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul centers probes

#print axioms wholeSample_is_original_evaluation
#print axioms exact_aggregate_client
#print axioms whole_address_count
end
end A2R45Literal
