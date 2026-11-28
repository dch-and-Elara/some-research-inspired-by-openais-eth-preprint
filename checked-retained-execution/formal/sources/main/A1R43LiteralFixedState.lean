import A1R43LiteralAdmission
import A1R43LiteralRegister

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxRecDepth 1800

/-! Direct fused version of the algebraic slot theorem, on the actual
selected active root. No assumption about its computed register value. -/
namespace A1R43Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R10Integral J6R11Integral J6R11Repack J6R12Blueprint
open J6ActiveRun J1PPrinted J6R9Recursive
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
variable (W : PairPlan F (smallA (Nat.card (Occ F))) (copies (Nat.card (Occ F))))
variable (f : ℤ[X])
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s
local notation "root" => starRoot F W f

theorem chosen_source_star_polynomial (guard : PrintedMargins m)
    (cubic : ∀ v,GraphCutMoments.degree F v=3) (d : @J6R12Blueprint.Ready f 1 S Δ root)
    (p : ℕ) (hp : 0<p) (hf : f.Monic) (hF : 0<f.natDegree) :
    letI := (root).host.finiteEdge
    letI := (root).host.finiteRow
    letI := (root).host.finiteCol
    let t := negativeCenter F W f guard
    (J6R14ZeroMode.polynomial (packing (starSelector F W f guard) d)
      (centerIndex d t) t.val p (root).host.file hf).eval 0 =
      (independentCount F:Box f 1 p) := by
  dsimp only
  letI : Fintype (Spare F W) := starFillFinite F W
  let t := negativeCenter F W f guard
  exact actual_named_zero_mode F (packing (starSelector F W f guard) d)
    (centerIndex d t) (negative_at_index_zero F W f guard d) f (Fintype.card V+1)
    p (Nat.succ_pos _) hp hf hF (same_selected_predecessor F W f guard d)
    (fun v=>by rw [cubic]; decide)

#print axioms chosen_source_star_polynomial
end
end A1R43Literal
