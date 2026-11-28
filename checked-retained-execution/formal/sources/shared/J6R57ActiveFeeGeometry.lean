import J6R50PeakStartPrecision
import J6R16ModeCostUniform
import J6R23ScheduleWeightBounds

/-! The physical fields that enter an active arithmetic bill:
actual local edges, coefficient-basis size, interpolation width and
slot count, and the genuine nonzero-mode weight tape (not the menu). -/
namespace J6R57ActiveFee
open scoped Polynomial
open Polynomial J1PPrinted J6ActiveRun J6ActiveSchedule
open J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R24MeteredRecursion J6R22Active J6R23ScheduleWeight J6R32StatefulArithmetic J6R50Peak HermiteLoss

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 13000000
set_option Elab.async false
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}

include cfg in
theorem physical_edges_at_most_root_scale
    (p : Path sel r c) (stable : Stable s C r) : c.edges≤C*s :=
  (Nat.le_mul_of_pos_left c.edges (Nat.pow_pos (by decide : 0<(8:ℕ)))).trans
    (stable_reachable cfg sel p.reached stable).sizeByDepth

theorem actual_weight_words_count
    {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
    {t : Center (printedParams (f:=f) (ell:=ell) s) c} {q : ℕ}
    (I : SiteTape sel d t q) :
    I.words.length≤6*c.edges*registerPrecision (printedParams (f:=f) (ell:=ell) s) c t := by
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have numEdges : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  have n := physical_roster_length (packing sel d) (centerIndex d t) I.modes I.nodup I.allModes
  rw [numEdges] at n
  have eq := congrArg List.length I.weightMeaning
  simp only [List.length_map] at eq
  exact eq.trans_le n

include cfg in
theorem actual_centre_dimension_fields
    (p : Path sel r c) (stable : Stable s C r)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c) :
    let SP := printedParams (f:=f) (ell:=ell) s
    let lam := Nat.clog 2 s
    let a := SP.levelBits c.depth
    let u := SP.levelWidth c.depth
    let abs := absolutePrecision s r.edges r.prec
    f.natDegree=4*lam ∧ a≤lam ∧
      J9PrintedSchedule.probeCount c.edges (2^a)≤(C*s)*(2*2^lam)+1 ∧
      order c.edges u t.val≤4*(C*s) ∧
      c.prec≤abs ∧ registerPrecision SP c t≤abs ∧
      commonLoss a c.edges u≤(C*s)*(24*2^lam+4*(lam+1)) := by
  let SP := printedParams (f:=f) (ell:=ell) s
  let lam := Nat.clog 2 s
  let a := SP.levelBits c.depth
  let u := SP.levelWidth c.depth
  have e := physical_edges_at_most_root_scale (cfg:=cfg) p stable
  have aa : a≤lam := bits_le_lam lam c.depth
  have hl : (2:ℕ)^a≤2^lam := Nat.pow_le_pow_right (by decide) aa
  obtain ⟨hu,huM⟩ := (J6R12Integral.printedGuards cfg sel r stable).taper c p.reached on
  have pro : J9PrintedSchedule.probeCount c.edges (2^a)≤(C*s)*(2*2^lam)+1 := by
    change c.edges*(2*2^a-1)+1≤_
    apply Nat.add_le_add_right
    exact Nat.mul_le_mul e ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ hl))
  exact ⟨cfg.coefficient,aa,pro,(order_bound c.edges u t.val hu huM).trans (Nat.mul_le_mul_left 4 e),
    absolute_inherited_precision_cap cfg sel stable p,absolute_register_precision_cap cfg sel stable p on t,
    (simple_common_scale_cap aa hu huM).trans (Nat.mul_le_mul_right _ e)⟩

include cfg in
theorem actual_weight_words_at_absolute_scale
    (p : Path sel r c) (stable : Stable s C r)
    {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
    {t : Center (printedParams (f:=f) (ell:=ell) s) c} {q : ℕ}
    (I : SiteTape sel d t q) :
    I.words.length≤6*(C*s)*absolutePrecision s r.edges r.prec :=
  (actual_weight_words_count I).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 6 (physical_edges_at_most_root_scale (cfg:=cfg) p stable))
      (absolute_register_precision_cap cfg sel stable p d.active t))

#print axioms physical_edges_at_most_root_scale
#print axioms actual_weight_words_count
#print axioms actual_centre_dimension_fields
#print axioms actual_weight_words_at_absolute_scale
end J6R57ActiveFee
