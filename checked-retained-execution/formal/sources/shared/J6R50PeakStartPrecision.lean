
import J6R48DFSPath
import J6R24MeteredRecursionTight

/-! A coarser but absolute-start precision cap for the true J6
recursive schedule. It does not rebase the root's physical depth or
replace the actual incoming precision by a depth-zero assumption. -/
namespace J6R50Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R48DFS

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 10500000

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

def edgePrecisionSlope (s : ℕ) : ℕ :=
  32*2^(Nat.clog 2 s)+8*(Nat.clog 2 s+1)

def absolutePrecision (s rootEdges rootPrec : ℕ) : ℕ :=
  rootPrec+(32*rootEdges/29)*edgePrecisionSlope s

include cfg

theorem actual_register_additive_increment (hr : Stable s C r) (p : Path sel r c)
    (ac : (S).cutoff<c.edges) (t : Center S c) :
    registerPrecision S c t≤c.prec+c.edges*edgePrecisionSlope s := by
  let a := (S).levelBits c.depth
  let u := (S).levelWidth c.depth
  let lam := Nat.clog 2 s
  obtain ⟨hu,huM⟩ := (J6R12Integral.printedGuards cfg sel r hr).taper _ p.reached ac
  have hH : height c.edges u≤4*c.edges := simple_height_cap hu huM
  have ha : a≤lam := bits_le_lam _ _
  have hD : (2:ℕ)^a/2^padicValInt 2 t.val≤(2:ℕ)^lam :=
    (Nat.div_le_self _ _).trans (Nat.pow_le_pow_right (by decide) ha)
  change c.prec+8*height c.edges u*(2^a/2^padicValInt 2 t.val)+8*c.edges*(a+1)≤_
  calc
    _≤c.prec+8*(4*c.edges)*2^lam+8*c.edges*(lam+1) :=
      Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hH) hD) _)
        (Nat.mul_le_mul_left _ (Nat.succ_le_succ ha))
    _=_ := by unfold edgePrecisionSlope lam; ring

theorem actual_path_inherited_precision (hr : Stable s C r) (p : Path sel r c) :
    c.prec+c.edges*edgePrecisionSlope s≤
      r.prec+(edgeStack p).sum*edgePrecisionSlope s := by
  induction p with
  | root => simp [edgeStack]
  | @step par p w ih =>
    have inc := actual_register_additive_increment cfg sel hr p w.property w.val.1
    change ((Plan sel).child par w).prec≤par.prec+par.edges*edgePrecisionSlope s at inc
    simp only [edgeStack,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_mul]
    omega

theorem absolute_inherited_precision_cap (hr : Stable s C r) (p : Path sel r c) :
    c.prec≤absolutePrecision s r.edges r.prec := by
  have geom := edgeStack_geometric p
  have fit : (edgeStack p).sum≤32*r.edges/29 := by omega
  exact (Nat.le_add_right _ _).trans ((actual_path_inherited_precision cfg sel hr p).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ fit) _))

theorem absolute_register_precision_cap (hr : Stable s C r) (p : Path sel r c)
    (ac : (S).cutoff<c.edges) (t : Center S c) :
    registerPrecision S c t≤absolutePrecision s r.edges r.prec := by
  have geom := edgeStack_geometric p
  have fit : (edgeStack p).sum≤32*r.edges/29 := by omega
  exact (actual_register_additive_increment cfg sel hr p ac t).trans
    ((actual_path_inherited_precision cfg sel hr p).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ fit) _))

/-- For a nonempty ancestry, its final parent was active under the
absolute printed depth and therefore already in the legal range.
The root-only stack has zero moves regardless of its absolute depth. -/
theorem actual_ancestry_moves_any_start (hr : Stable s C r) (p : Path sel r c) :
    moves p≤pathLimit s C := by
  cases p with
  | root => exact Nat.zero_le _
  | @step parent p w =>
    have stable := stable_reachable cfg sel p.reached hr
    have active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)<parent.edges := w.property
    have lam : 0<Nat.clog 2 s := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
    have hp := active_depth_power s (Nat.clog 2 s) C parent.edges parent.depth lam active stable.sizeByDepth
    have hD := Nat.le_log_of_pow_le (by decide : 1<(8:ℕ)) hp
    have he := (stack_exact_depth p).1
    unfold pathLimit
    change moves p+1≤_
    omega

#print axioms actual_register_additive_increment
#print axioms actual_path_inherited_precision
#print axioms absolute_inherited_precision_cap
#print axioms absolute_register_precision_cap
#print axioms actual_ancestry_moves_any_start
end J6R50Peak
