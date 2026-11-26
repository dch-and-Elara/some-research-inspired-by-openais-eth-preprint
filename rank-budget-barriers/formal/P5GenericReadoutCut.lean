import P5GenericReadoutIntrinsic

/-! The exact rho(lambda) rank charge for the SAME oriented matching
flattening used by v7, including arbitrary opposite-side functions. -/
namespace Paper5.GenericReadout
open Matrix Module SeparatedRank FiniteAlgebraReadout
open scoped BigOperators Classical

variable {K A V I T : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem cut_readout_rank (t : LocalReadout (V:=V) (K:=K) (A:=A))
    (e : (I × Bool) ↪ V) :
    (Matrix.of fun x y=>t.value (pinnedSigns e x y)).rank≤
      rho t.read * 2^(Fintype.card I-endpointImbalance e t.side) := by
  obtain ⟨f,g,h⟩ := (exact_intrinsic_readout_capacity t.read).1
  let Z (j : Fin (rho t.read)) : VertexTerm V K :=
    { side := t.side
      coeff := 1
      onCut := fun x=>f j (t.left x)
      offCut := fun y=>g j (t.right y) }
  have hv (σ : V→Bool) : t.value σ=∑j,(Z j).value σ := by
    simpa only [LocalReadout.value,Z,VertexTerm.value,one_mul] using
      h (t.left (CutTerm.restrict t.side σ)) (t.right (CutTerm.restrict t.sideᶜ σ))
  rw [vertex_restriction_sum Z _ hv e]
  refine (rank_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j : Fin (rho t.read),2^(Fintype.card I-endpointImbalance e t.side) :=
      Finset.sum_le_sum fun j _=>(Z j).onTransversal e |>.rank_le
    _ = _ := by simp

variable [Fintype T]

theorem many_readouts_same_flattening (t : T → LocalReadout (V:=V) (K:=K) (A:=A))
    (F : (V→Bool)→K) (hF : ∀σ,F σ=∑u,(t u).value σ)
    (e : (I × Bool) ↪ V) :
    (Matrix.of fun x y=>F (pinnedSigns e x y)).rank≤
      ∑ u,rho (t u).read*2^(Fintype.card I-endpointImbalance e (t u).side) := by
  have h : (Matrix.of fun x y=>F (pinnedSigns e x y)) =
      ∑u,Matrix.of (fun x y=>(t u).value (pinnedSigns e x y)) := by
    apply Matrix.ext
    intro x y
    simpa only [Matrix.of_apply,Matrix.sum_apply] using hF (pinnedSigns e x y)
  rw [h]
  exact (rank_sum_le _ _).trans (Finset.sum_le_sum fun u _=>cut_readout_rank (t u) e)

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype T] in
theorem rho_collected_upper (s : Finset T) (read : T→A→ₗ[K]K) :
    rho (∑i∈s,read i)≤∑i∈s,rho (read i) := by
  let b := Module.finBasis K A
  have he : P5A2.pairing b (∑i∈s,read i)=∑i∈s,P5A2.pairing b (read i) := by
    apply Matrix.ext
    intro u v
    simp only [P5A2.pairing,Matrix.of_apply,Matrix.sum_apply,LinearMap.sum_apply]
  calc
    _ = capacity b (∑i∈s,read i) := (capacity_eq_rho b _).symm
    _ = (∑i∈s,P5A2.pairing b (read i)).rank := by rw [capacity,he]
    _ ≤ ∑i∈s,capacity b (read i) := rank_sum_le _ _
    _ = _ := Finset.sum_congr rfl (fun i _=>capacity_eq_rho b (read i))

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype T] in
theorem exact_same_register_cancellation (read : A→ₗ[K]K) :
    rho (read+(-read))=0 := by
  rw [add_neg_cancel,←capacity_eq_rho (Module.finBasis K A),capacity_of_zero]

#print axioms cut_readout_rank
#print axioms many_readouts_same_flattening
#print axioms rho_collected_upper
#print axioms exact_same_register_cancellation
end Paper5.GenericReadout
