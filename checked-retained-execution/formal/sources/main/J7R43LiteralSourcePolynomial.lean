import J7R43LiteralSlots
import J6R14ZeroModeDegree

/-! J7's omitted-zero semantic fallback. The actual single *source*
group at fixed singleton mode is one finite polynomial in ζ. Its extra
moment is a constant in ζ, so it does not raise the printed degree. -/
namespace J7R43Literal
open scoped Classical Polynomial BigOperators
open Polynomial P1DyadicGrid P11FullPacking J6R9Recursive
open J6R10Repack J6R9PacketScopes J6R10PacketAssembly J6R11Integral J6R10Integral J6R9PacketChild
open J6R14ZeroMode
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
variable (p : ℕ) (old : EntryFile f ell N) (hf : f.Monic) (m : Mode i p P.mask)
local notation "g" => (source P.mask i m)

def literalSourcePolynomial : (Box f ell p)[X] :=
  ∑ v : PhysicalState P i g, C (oldState P i g p old hf v * stateMoment P i g p v m) *
    ∏ k, packetPoly P i t p g k v

set_option maxHeartbeats 2300000 in
theorem literal_source_polynomial_eval (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (z : Box f ell p) :
    (literalSourcePolynomial P i t p old hf m).eval z =
      reduce p f ell (actualChildTruth P i ht hv p z old hf (Finsupp.single m 1) g) := by
  change (evalRingHom z) (literalSourcePolynomial P i t p old hf m) = _
  rw [literal_singleton_child P i p z old hf ht hv m,literalSourcePolynomial,map_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [map_mul,map_prod,coe_evalRingHom,eval_C,packetPoly,affinePoly_eval,actualBaselineWeight]
  ring

set_option maxHeartbeats 2100000 in
theorem literal_source_polynomial_degree (ht : t ∈ grid a) :
    (literalSourcePolynomial P i t p old hf m).natDegree ≤
      J9PrintedSchedule.degreeBound (Fintype.card E) (2^a) := by
  let d := 2*2^a-1
  let n (h : G) : ℕ := ∑ k, ∑ _r ∈ actualRows (childBlock P i) h k, d
  have hchild : (literalSourcePolynomial P i t p old hf m).natDegree ≤ n g := by
    unfold literalSourcePolynomial
    apply natDegree_sum_le_of_forall_le
    intro v _
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C,zero_add]
    refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    unfold packetPoly
    exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun r _ => affinePoly_degree P i t p ht g v r)
  calc
    _ ≤ n g := hchild
    _ ≤ ∑ h, n h := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    _ = _ := sum_packet_rows (childBlock P i) d

#print axioms literalSourcePolynomial
#print axioms literal_source_polynomial_eval
#print axioms literal_source_polynomial_degree
end
end J7R43Literal
