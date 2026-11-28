import J6R48DFSPath
import J6R75RawPeakLayoutWords
import J6R68ActiveInputsBudget

/-! Division-free simultaneous allowance for one named pair backing
per frame on the actual Appendix D occurrence path. The literal
source shrink is 32 Mchild <= 3 Mparent. No reclamation of ancestor
backings is assumed, and siblings are not claimed to be live. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R32StatefulArithmetic J6R48DFS J6R68ActiveInputs V8NativeMessage.N2DLabels
open P11FullPacking J6R10Repack

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3650
set_option maxHeartbeats 7200000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}
local notation "P" => (@Plan f ell s sel)

def physicalPairStackSquares (p : Path sel r c) : ℕ :=
  ((edgeStack p).map (fun e=>e*e)).sum

theorem real_layout_pair_slots_have_the_squared_path_potential (p : Path sel r c) :
    1015*physicalPairStackSquares p+9*(c.edges*c.edges)≤1024*(r.edges*r.edges) := by
  induction p with
  | root=>
    simp only [physicalPairStackSquares,edgeStack,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    omega
  | @step par p w ih=>
    let n := ((P).child par w).edges
    let m := par.edges
    have shrink : 32*n≤3*m := child_edge_shrink w
    have sq : 1024*(n*n)≤9*(m*m) := by
      calc
        1024*(n*n)=(32*n)*(32*n) := by ring
        _≤(3*m)*(3*m) := Nat.mul_le_mul shrink shrink
        _=9*(m*m) := by ring
    have shape :
      physicalPairStackSquares (.step p w)=physicalPairStackSquares p+n*n := by
      simp only [physicalPairStackSquares,edgeStack,List.map_append,List.map_cons,List.map_nil,
        List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,n]
    rw [shape]
    change 1015*(physicalPairStackSquares p+n*n)+9*(n*n)≤_
    change 1015*physicalPairStackSquares p+9*(m*m)≤_ at ih
    omega

def namedPairBitsAlong
    (bits : ∀ {u : Call (PhysicalHost f ell)},Path sel r u→ℕ) :
    {u : Call (PhysicalHost f ell)}→Path sel r u→ℕ
  | _,.root=>bits .root
  | _,.step p w=>namedPairBitsAlong bits p+bits (.step p w)

theorem one_pair_bank_per_true_path_frame_fits_a_single_squared_roof
    (weights : ∀ {u : Call (PhysicalHost f ell)},Path sel r u→ℕ) (recordBits : ℕ)
    (certify : ∀ {u : Call (PhysicalHost f ell)} (p : Path sel r u),
      weights p≤recordBits*(u.edges*u.edges)) (p : Path sel r c) :
    1015*namedPairBitsAlong weights p≤1024*recordBits*(r.edges*r.edges) := by
  have widths : namedPairBitsAlong weights p≤recordBits*physicalPairStackSquares p := by
    induction p with
    | root=>
      simpa only [namedPairBitsAlong,physicalPairStackSquares,edgeStack,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,Nat.add_zero] using certify (.root : Path sel r r)
    | @step par p w ih=>
      simpa only [namedPairBitsAlong,physicalPairStackSquares,edgeStack,List.map_append,List.map_cons,
        List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add] using
        Nat.add_le_add ih (certify (.step p w))
  calc
    1015*namedPairBitsAlong weights p≤1015*(recordBits*physicalPairStackSquares p) :=
      Nat.mul_le_mul_left _ widths
    _=recordBits*(1015*physicalPairStackSquares p) := by ring
    _≤recordBits*(1024*(r.edges*r.edges)) := Nat.mul_le_mul_left _
      ((Nat.le_add_right _ _).trans (real_layout_pair_slots_have_the_squared_path_potential p))
    _=_ := by ring
end

theorem actual_layout_pair_record_width_from_source_scales {E R C : Type*}
    [Fintype E] [Fintype R] [Fintype C] {a q K : ℕ} {N : Network E R C}
    (I : Full64Input N a) (dims : LayoutScales I q K) :
    2*fullEdgeLayoutWidth I.format.kR I.format.kC I.format.b≤28*K+4 := by
  have b : I.format.b≤6*K := I.labelWidth.symm ▸ Nat.mul_le_mul_left 6 dims.dimension
  have r := dims.rowWord
  have c := dims.colWord
  unfold fullEdgeLayoutWidth
  omega

#print axioms real_layout_pair_slots_have_the_squared_path_potential
#print axioms one_pair_bank_per_true_path_frame_fits_a_single_squared_roof
#print axioms actual_layout_pair_record_width_from_source_scales
end J6R75RawPeak
