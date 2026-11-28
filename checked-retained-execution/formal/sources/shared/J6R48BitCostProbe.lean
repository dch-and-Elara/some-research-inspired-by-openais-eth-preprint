import J6R48BitCostKernels

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6800000
set_option maxRecDepth 1800

/-! Count the arithmetic iteration roster on the genuine dependent
Plan slots, with multiplicity. This proof-side unit receipt is never
used as an evaluator; it only counts actual centre/probe/mode/group
addresses, including two addresses that create equal Call records. -/
namespace J6R48BitCost
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R22Active J6R24MeteredRecursion J6R9Recursive
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

theorem sum_constant_receipts {X : Type*} (xs : List X) (f : X→ℕ) (e : ℕ)
    (same : ∀ x∈xs,f x=e) : (xs.map f).sum=xs.length*e := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hf := same x List.mem_cons_self
    have ht := ih (fun y hy=>same y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons,hf,ht,Nat.add_mul,Nat.one_mul]
    omega

theorem site_unit_occurrences {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode)
    (unit : ∀ z β (g : Fin 64),(I.child z β g).steps=1) :
    I.childBill=n*I.modes.length*64 := by
  have eg (z : Fin n) (β : Mode) : bill (I.child z β) (groupOrder 64)=64 := by
    unfold bill
    rw [sum_constant_receipts (groupOrder 64) _ 1 (fun g _=>unit z β g),groupOrder,List.length_ofFn]
  have ez (z : Fin n) : probeEntryBill I.modes (I.child z)=I.modes.length*64 := by
    unfold probeEntryBill
    exact sum_constant_receipts I.modes _ 64 (fun β _=>eg z β)
  unfold SiteTape.childBill
  rw [sum_constant_receipts (probeOrder n) _ _ (fun z _=>ez z),probeOrder,List.length_ofFn]
  exact (Nat.mul_assoc n I.modes.length 64).symm

/-- Literal full Lagrange pass: n coefficients at n probes. The R24
resident routine normally asks for the shorter jet; this is a distinct
choice of output width on one and the same grouped sample stream. -/
def fullMesh {p ell k n : ℕ} {Mode : Type*} (I : SiteTape p ell k n Mode) (hn : 0<n) :
    Meter (JetTape I.fw ell n) :=
  interpPrefix I.hp I.nonempty I.he hn I.nodeM I.groupedM

theorem full_lagrange_arithmetic {p ell k n : ℕ} {Mode : Type*}
    (I : SiteTape p ell k n Mode) (hn : 0<n) :
    (fullMesh I hn).steps ≤
      n * bill I.nodeM (probeOrder n) + I.childBill +
        n * probeExtra I.fw.length ell p 64 I.modes.length I.hp +
        interpExtra I.fw.length ell p n n I.hp := by
  have hi := I.interp_bill
  rw [site_probe_reload_exact] at hi
  exact (interpPrefix_steps I.hp I.nonempty I.he hn I.nodeM I.groupedM).trans
    (Nat.add_le_add_right hi _)

#print axioms sum_constant_receipts
#print axioms site_unit_occurrences
#print axioms fullMesh
#print axioms full_lagrange_arithmetic
end J6R48BitCost

