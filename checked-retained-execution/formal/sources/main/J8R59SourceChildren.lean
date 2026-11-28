import J6R16SpecializedBoxRunProduct
import J6R12RepackGenerated

/-! Plug a prescribed binary word into the actual packet factory. The
old file, selected packing, center, order, tuple and precision do not
change. A new external roster may contain legal words not in the frozen
enumerator; at any word that does agree, the child calls are identical.
The same checked descendant source recursion is used in both cases. -/
namespace J8R59
open scoped Classical BigOperators Polynomial
open Polynomial NativeProbeRing J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R9PacketScopes J6R10Repack J6R10Integral J6R11Blueprint J6R12Blueprint
open J6R11Repack J6R12Integral J9R15FrozenErasurePhysical J6R14SpecializedBox J1PPrinted

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell size C : ℕ}
local notation "P₀" => (printedParams (f:=f) (ell:=ell) size)
local notation "Δ₀" => (sourceDelta size)

variable (sel : Selector (printedParams (f:=f) (ell:=ell) size) (sourceDelta size))
variable {c : Call (PhysicalHost f ell)}
variable (rd : @J6R12Blueprint.Ready f ell (printedParams (f:=f) (ell:=ell) size) (sourceDelta size) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) size) c)
variable (addr : Fin f.natDegree → Bool) (β : LiteralMenu sel rd t) (g : Fin 64)
local notation "p₀" => (registerPrecision P₀ c t)

def wordNode : Box f ell p₀ :=
  J6ActiveInterpolation.scalarIn p₀ f ell (NativeProbeRing.probe p₀ f addr)

def wordPacketHost : PhysicalHost f ell := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact actualPacketHost (packing sel rd) (centerIndex rd t) (centerNonzero t) rfl
    p₀ (box_two_nil p₀ f ell) (wordNode (size:=size) (c:=c) t addr) c.host.file β.val g

def wordPacketCall : Call (PhysicalHost f ell) :=
  let child := wordPacketHost sel rd t addr β g
  ⟨child,c.depth+1,child.edgeCount,p₀⟩

theorem word_child_agrees_on_original_address (i : Probe P₀ c)
    (h : addr=chosenRep f.natDegree _ rd.fit i) :
    wordPacketCall sel rd t addr β g = samePacketCall (s:=size) (c:=c) sel rd t i β g := by
  subst addr
  rfl

set_option maxHeartbeats 2400000 in
theorem word_child_stable (seed : Stable size C c) :
    Stable size C (wordPacketCall sel rd t addr β g) := by
  let child := wordPacketHost sel rd t addr β g
  have hP : c.prec ≤ p₀ :=
    (child_monotone c.prec _ _ _ t.val (Nat.zero_lt_of_lt rd.active)).le
  have hM : 0<c.host.edgeCount := rd.edgeCount.symm ▸ Nat.zero_lt_of_lt rd.active
  have hgen := J6R12Repack.generated_invariants (H:=c.host)
    (packing sel rd) (centerIndex rd t) (centerNonzero t) rfl c.prec p₀
    (box_two_nil p₀ f ell) (wordNode (size:=size) (c:=c) t addr) β.val g Δ₀
    (Fintype.card_fin 64) hM rd.degree rd.packetDegree rd.tags hP
  change GoodDegree child Δ₀ ∧ GoodTags child p₀ ∧
    32*child.edgeCount≤3*c.host.edgeCount ∧ child.edgeCount<c.host.edgeCount at hgen
  have hcut : 8*child.edgeCount≤c.edges := by
    have h := hgen.2.2.1
    rw [rd.edgeCount] at h
    omega
  change Stable size C ⟨child,c.depth+1,child.edgeCount,p₀⟩
  refine ⟨rfl,hgen.1,hgen.2.1,?_⟩
  change 8^(c.depth+1)*child.edgeCount≤C*size
  rw [pow_succ,mul_assoc]
  exact (Nat.mul_le_mul_left _ hcut).trans seed.sizeByDepth

def wordReply (hf : f.Monic) : Box f ell p₀ :=
  let r := wordPacketCall sel rd t addr β g
  (J6R12Blueprint.sourceBlueprint sel r hf).program.run r

def wordCompleted (hf : f.Monic) : Box f ell p₀ :=
  ∏ g : Fin 64, wordReply sel rd t addr β g hf

theorem word_completed_agrees_on_original_address (i : Probe P₀ c) (hf : f.Monic)
    (h : addr=chosenRep f.natDegree _ rd.fit i) :
    wordCompleted sel rd t addr β hf = printedPacketProduct (s:=size) (c:=c) sel rd t i β hf := by
  subst addr
  rfl

set_option maxHeartbeats 4100000 in
theorem word_completed_is_actual_projection
    (cfg : RootBounds size C f) (seed : Stable size C c) (hf : f.Monic)
    (hF : 0<f.natDegree) [Fact (Irreducible (residuePoly f))] :
    wordCompleted sel rd t addr β hf =
      (letI := c.host.finiteEdge
       letI := c.host.finiteRow
       letI := c.host.finiteCol
       actualProjection (packing sel rd) (centerIndex rd t) (centerNonzero t) rfl
        p₀ (wordNode (size:=size) (c:=c) t addr) c.host.file hf β.val) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  unfold wordCompleted actualProjection
  refine Finset.prod_congr rfl ?_
  intro j _
  unfold wordReply
  rw [printed_run_exact cfg sel _ (word_child_stable sel rd t addr β j seed) hf hF]
  apply congrArg (reduce p₀ f ell)
  exact actualPacketHost_truth (packing sel rd) (centerIndex rd t) (centerNonzero t) rfl
    p₀ (wordNode (size:=size) (c:=c) t addr) c.host.file hf β.val j

#print axioms word_child_agrees_on_original_address
#print axioms word_child_stable
#print axioms word_completed_agrees_on_original_address
#print axioms word_completed_is_actual_projection
end
end J8R59
