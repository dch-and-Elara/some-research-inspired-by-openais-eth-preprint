import J6R57ActiveFeeArithmetic
import J6R22ActiveBinary
import J6R22ActiveInterpolate

/-! Count the actual repeated node-mask accesses in the source
interpolator, including the off-diagonal reads. The paid mask supplier
is explicit; its fee is not inferred from correctness of its bits. -/
namespace J6R57ActiveFee
open AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000
set_option maxRecDepth 2400
set_option Elab.async false

theorem actual_list_charges {A : Type*} (xs : List A) (run : A→ℕ) (each : ℕ)
    (ok : ∀ x∈xs,run x≤each) : (xs.map run).sum≤xs.length*each := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using
      Nat.add_le_add (ok x List.mem_cons_self) (ih (fun y hy=>ok y (List.mem_cons_of_mem _ hy)))

theorem exact_probe_mask_read_envelope {p ell n K maskFee : ℕ} {fw : List (Word p)}
    (hp : 0<p) (hv : 0<ell)
    (mask : Fin n→Meter {bits : List Bool // bits.length=fw.length})
    (he : fw.length≤K) (hℓ : ell≤K) (hP : p≤K) (hn : n≤K)
    (charged : ∀ i,(mask i).steps≤maskFee) :
    let node := fun i=>padCost (encodeProbe hp hv (mask i).result) (mask i).steps
    ((probeOrder n).map (needsAt node)).sum≤
      K*K*(maskFee+K*(K+6)+5*(K+1)^3+2) := by
  let node := fun i=>padCost (encodeProbe hp hv (mask i).result) (mask i).steps
  let cap := maskFee+K*(K+6)+5*(K+1)^3+2
  have read (i : Fin n) : (node i).steps≤cap := by
    have W := uvWidth_physical_poly he hℓ hP
    have G := Nat.mul_le_mul he (Nat.add_le_add_right hP 6)
    have H := charged i
    change (encodeProbe hp hv (mask i).result).steps+(mask i).steps≤cap
    rw [encodeProbe_cost]
    unfold cap
    omega
  have one (i : Fin n) : needsAt node i≤n*cap := by
    have rest := actual_list_charges (offDiagonal i) (fun q=>(node q).steps) cap (fun q _=>read q)
    rw [offDiagonal_length] at rest
    unfold needsAt bill
    calc
      _≤cap+(n-1)*cap := Nat.add_le_add (read i) rest
      _=(n-1+1)*cap := by ring
      _=n*cap := congrArg (fun r : ℕ=>r*cap)
        (Nat.sub_add_cancel (Nat.succ_le_of_lt ((Nat.zero_le i.val).trans_lt i.isLt)))
  have sum := actual_list_charges (probeOrder n) (needsAt node) (n*cap) (fun i _=>one i)
  have size : (probeOrder n).length=n := List.length_ofFn
  rw [size] at sum
  exact sum.trans ((Nat.mul_le_mul hn (Nat.mul_le_mul_right _ hn)).trans_eq (by unfold cap; ring))

#print axioms actual_list_charges
#print axioms exact_probe_mask_read_envelope
end J6R57ActiveFee
