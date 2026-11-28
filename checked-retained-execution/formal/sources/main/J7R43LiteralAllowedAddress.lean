import J7R43LiteralAllowedZero

/-! A zero-containing list at the exact printed probe count. This is
an allowed paper schedule, not a claim that the frozen prefix contains
the all-false word. Its first actual numeric sample is the source call. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial NativeProbeRing J6ActiveInterpolation J6ActiveRun J6R9Recursive
open J6R12Blueprint J6R11Blueprint J1PPrinted J6R12Integral
open J6R10Repack J6R10Integral
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell s : ℕ} {c : Call (PhysicalHost f ell)}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)

set_option maxHeartbeats 3200000 in
include d in
theorem chosen_legal_list_with_zero (hf : f.Monic) (hF : 0<f.natDegree)
    [Fact (Irreducible (residuePoly f))] :
    let S := printedParams (f:=f) (ell:=ell) s
    let p := registerPrecision S c t
    ∃ words : Probe S c → Fin f.natDegree→Bool,
      Function.Injective words ∧
      (∀ i j, i≠j → IsUnit (scalarIn p f ell (probe p f (words j)) -
        scalarIn p f ell (probe p f (words i)))) ∧
      ∃ j, j.val=0 ∧ scalarIn p f ell (probe p f (words j))=0 := by
  let S := printedParams (f:=f) (ell:=ell) s
  let p := registerPrecision S c t
  let n := J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth)
  have hn : 0<n := by unfold n J9PrintedSchedule.probeCount; omega
  let words := zeroFirstWords f.natDegree n d.fit hn
  refine ⟨words,zeroFirstWords_injective _ _ _ _,?_,⟨⟨0,hn⟩,rfl,?_⟩⟩
  · intro i j hij
    exact zero_first_list_units p (register_positive d t) hf hF n d.fit hn i j hij
  · change scalarIn p f ell (probe p f (zeroFirstWords f.natDegree n d.fit hn ⟨0,hn⟩))=0
    rw [zeroFirstWords_first,J6R14ZeroMode.actual_probe_zero,map_zero]

set_option maxHeartbeats 3200000 in
theorem legal_zero_word_construction_is_same_call
    (β : LiteralMenu sel d t) (g : Fin 64)
    (word : Fin f.natDegree→Bool) (hword : word=fun _ => false) :
    allowedZeroCall (s:=s) (c:=c) sel d t β g =
      (let S := printedParams (f:=f) (ell:=ell) s
       let p := registerPrecision S c t
       letI := c.host.finiteEdge
       letI := c.host.finiteRow
       letI := c.host.finiteCol
       let H := actualPacketHost (packing sel d) (centerIndex d t) (centerNonzero t) rfl
         p (box_two_nil p f ell) (scalarIn p f ell (probe p f word))
         c.host.file β.val g
       ⟨H,c.depth+1,H.edgeCount,p⟩) := by
  subst word
  have H (p : ℕ) : scalarIn p f ell (probe p f (fun _ => false)) = 0 := by
    rw [J6R14ZeroMode.actual_probe_zero,map_zero]
  simp only [H]
  rfl

#print axioms chosen_legal_list_with_zero
#print axioms legal_zero_word_construction_is_same_call
end
end J7R43Literal