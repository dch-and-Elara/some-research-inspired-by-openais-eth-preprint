import J6R14ZeroModePolynomial

/-! The number of affine factors in the zero-mode polynomial is exactly
the number of real original row wires, not the padded number of slots. -/
namespace J6R14ZeroMode
open scoped Classical Polynomial BigOperators
open Polynomial P1DyadicGrid P11FullPacking J6R9Recursive
open J6R10Repack J6R10PacketAssembly J6R11Integral
noncomputable section

theorem sum_packet_rows {I G K : Type*} [Fintype I] [Fintype G] [Fintype K]
    [DecidableEq G] [DecidableEq K] (block : I → G × K) (d : ℕ) :
    (∑ g, ∑ k, ∑ _r ∈ actualRows block g k, d) = Fintype.card I*d := by
  let F (b : G × K) : ℕ := ∑ r : I, if block r=b then d else 0
  have h (g : G) (k : K) : (∑ _r ∈ actualRows block g k,d) = F (g,k) := by
    rw [actualRows,Finset.sum_filter]
  simp_rw [h]
  rw [← Fintype.sum_prod_type F]
  dsimp only [F]
  rw [Finset.sum_comm]
  simp

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

theorem degree (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (p : ℕ)
    (ht : t ∈ grid a) (file : EntryFile f ell N) (hf : f.Monic) :
    (polynomial P i t p file hf).natDegree ≤ J9PrintedSchedule.degreeBound (Fintype.card E) (2^a) := by
  let d := 2*2^a-1
  let n (g : G) : ℕ := ∑ k, ∑ _r ∈ actualRows (childBlock P i) g k, d
  have hchild (g : G) : (childPoly P i t p file hf g).natDegree ≤ n g := by
    unfold childPoly
    apply natDegree_sum_le_of_forall_le
    intro v _
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C,zero_add]
    refine (natDegree_prod_le _ _).trans ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    unfold packetPoly
    refine (natDegree_prod_le _ _).trans ?_
    exact Finset.sum_le_sum (fun r _ => affinePoly_degree P i t p ht g v r)
  unfold polynomial
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ g, n g := Finset.sum_le_sum fun g _ => hchild g
    _ = _ := sum_packet_rows (childBlock P i) d

#print axioms sum_packet_rows
#print axioms degree
end
end J6R14ZeroMode
