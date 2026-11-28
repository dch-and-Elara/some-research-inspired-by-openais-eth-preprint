
import A2R45LiteralAdmission
import A2R45LiteralSlot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000
set_option synthInstance.maxHeartbeats 130000
set_option maxRecDepth 1950
set_option linter.unusedSectionVars false

/-! On the actual selected root, the genuine switch tensor's root
polynomial is exact at the named center and zero probe. Keep the
precision parametric, so the state proof does not need to normalize the
large concrete printed precision when comparing receiver types. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R10Integral J6R11Integral J6R11Repack J6R12Blueprint
open J6ActiveRun J1PPrinted J6R9Recursive
open FixedHostAcquisition

noncomputable section
variable {n : ℕ} (W : Plan n) (w : Input n) (f : ℤ[X])
local notation "m" => simCount n
local notation "s" => A1R43Literal.starSize m
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s
local notation "root" => rootCall W w f

theorem actual_chosen_source_polynomial (guard : A1R43Literal.PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ root) (p : ℕ)
    (hp : 0<p) (hf : f.Monic) (hF : 0<f.natDegree) (hn : 0<n) :
    letI := (root).host.finiteEdge
    letI := (root).host.finiteRow
    letI := (root).host.finiteCol
    let t := negativeCenter W w f guard
    (J6R14ZeroMode.polynomial
      (@packing f 1 S Δ root (fixedSelector W w f guard) d)
      (@centerIndex f 1 S Δ root d t) t.val p (root).host.file hf).eval 0 =
      (count w.enabled:Box f 1 p) := by
  dsimp only
  let t := negativeCenter W w f guard
  let finitePad : Fintype (FilledPad W) := inferInstance
  exact @native_zero_polynomial n (FilledPad W) finitePad ((S).levelBits (root).depth)
    (@packing f 1 S Δ root (fixedSelector W w f guard) d)
    (@centerIndex f 1 S Δ root d t) (negative_at_index_zero W w f guard d)
    w f (n+2) p (Nat.succ_pos _) hp hf hF hn
    (same_selected_predecessor W w f guard d)

#print axioms actual_chosen_source_polynomial
end
end A2R45Literal
