import J6R50PeakStartPrecision
import J6R57LeafCapPacket

/-! Recover absolute inherited precision and native mode-count size
from the same printed source parameter. For a nonzero-depth entry
point the true initial native precision is retained in the bound. -/
namespace J6R58LeafScale
open scoped Polynomial
open J1PPrinted J6R16ModeCost J6R50Peak J6R48DFS J6R32StatefulArithmetic
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

theorem printed_clog_power_le_twice_size (s : ℕ) (hs : 1<s) :
    (2:ℕ)^(Nat.clog 2 s)≤2*s := by
  let l := Nat.clog 2 s
  have pos : 0<l := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2 (by simpa using hs)
  have low : 2^(l-1)<s := Nat.pow_pred_clog_lt_self (by decide : 1<2) hs
  have next : l=l-1+1 := by omega
  calc
    2^l=2^(l-1)*2 := by conv_lhs => rw [next]; rw [pow_succ]
    _≤2*s := by rw [Nat.mul_comm _ 2]; exact Nat.mul_le_mul_left 2 low.le

theorem source_precision_slope_linear (s : ℕ) (hs : 1<s) :
    edgePrecisionSlope s≤80*s := by
  have hp := printed_clog_power_le_twice_size s hs
  have hl := (J9PrintedSchedule.next_le_two_power (Nat.clog 2 s)).trans hp
  unfold edgePrecisionSlope
  have h := Nat.add_le_add (Nat.mul_le_mul_left 32 hp) (Nat.mul_le_mul_left 8 hl)
  exact h.trans_eq (by ring)

theorem absolute_precision_from_printed_source (s C rootEdges initial : ℕ)
    (hs : 1<s) (edges : rootEdges≤C*s) :
    absolutePrecision s rootEdges initial ≤ initial+160*C*s^2 := by
  have hSpan : 32*rootEdges/29≤2*(C*s) := by
    apply Nat.div_le_of_le_mul
    calc
      _≤32*(C*s) := Nat.mul_le_mul_left _ edges
      _≤58*(C*s) := Nat.mul_le_mul_right _ (by decide)
      _=_ := by ring
  unfold absolutePrecision
  have h := Nat.mul_le_mul hSpan (source_precision_slope_linear s hs)
  exact Nat.add_le_add_left (h.trans_eq (by ring)) _

theorem source_register_bound (s C modes precision : ℕ) (p0 : ℕ)
    (large : 1024≤Nat.clog 2 s) (smallC : C≤s) (rootPrec : p0≤C*s)
    (precisionFit : precision≤p0+160*C*s^2) (modeFit : modes≤3*(C*s)*precision) :
    modes+2≤2^(6*Nat.clog 2 s) := by
  let lam := Nat.clog 2 s
  have hsMaybe : 1<s := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).1 (show 0<lam by omega)
  have hs : 0<s := (by decide : (0:ℕ)<1).trans hsMaybe
  have hCs : C*s≤C*s^2 := Nat.mul_le_mul_left _ (by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ hs)
  have pFit : precision≤161*C*s^2 := by
    calc
      _≤p0+160*C*s^2 := precisionFit
      _≤C*s^2+160*C*s^2 := Nat.add_le_add_right (rootPrec.trans hCs) _
      _=_ := by ring
  have hM : modes+2≤483*s^5+2 := by
    calc
      _≤3*(C*s)*(161*C*s^2)+2 :=
        Nat.add_le_add_right (modeFit.trans (Nat.mul_le_mul_left _ pFit)) 2
      _≤3*(s*s)*(161*s*s^2)+2 := by gcongr
      _=_ := by ring
  have h9 : (485:ℕ)≤2^9 := by decide
  have powS : s≤2^lam := Nat.le_pow_clog (by decide) s
  calc
    _≤483*s^5+2 := hM
    _≤485*s^5 := by
      rw [show (485:ℕ)=483+2 by decide,Nat.add_mul]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.pow_pos hs)) _
    _≤2^9*(2^lam)^5 := Nat.mul_le_mul h9 (Nat.pow_le_pow_left powS 5)
    _=2^(9+lam*5) := by rw [←pow_mul,←pow_add]
    _≤_ := Nat.pow_le_pow_right (by decide) (by change 9+lam*5≤6*lam; omega)

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

include cfg in
theorem actual_source_path_edges_le (hr : Stable s C r) (par : Path sel r c) :
    c.edges≤C*s :=
  (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0<(8:ℕ)))).trans
    (stable_reachable cfg sel par.reached hr).sizeByDepth

include cfg in
theorem actual_native_register_quadratic (hr : Stable s C r) (par : Path sel r c)
    (active : (SP).cutoff<c.edges) (t : Center SP c) :
    registerPrecision SP c t≤r.prec+160*C*s^2 := by
  have hn : 1<s := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).1
    (show 0<Nat.clog 2 s from (by decide : (0:ℕ)<1024).trans_le (root_lambda_large cfg))
  have edges : r.edges≤C*s := actual_source_path_edges_le (cfg:=cfg) sel hr (.root : Path sel r r)
  exact (absolute_register_precision_cap cfg sel hr par active t).trans
    (absolute_precision_from_printed_source s C r.edges r.prec hn edges)

#print axioms printed_clog_power_le_twice_size
#print axioms source_precision_slope_linear
#print axioms absolute_precision_from_printed_source
#print axioms source_register_bound
#print axioms actual_source_path_edges_le
#print axioms actual_native_register_quadratic
end J6R58LeafScale
