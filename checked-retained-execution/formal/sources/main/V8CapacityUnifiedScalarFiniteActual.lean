import V8CapacityUnifiedScalarActual
import V8CapacityUnifiedScalarBasis

/-! S4 finite computation: raw values, not residue representatives,
give a finite monic vanishing polynomial in each variable. -/
namespace V8CapacityUnified.Scalar
open scoped Polynomial BigOperators Classical
open Polynomial V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable {O Z H : Type*} [CommRing O] [IsDomain O] [Fintype Z] [Nonempty Z] [Fintype H]

def scalarValues (u : Z → O) : Finset O := Finset.univ.image u

def scalarNull (u : Z → O) : O[X] := ∏ c ∈ scalarValues u, (X-C c)

theorem scalarNull_monic (u : Z → O) : (scalarNull u).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem scalarNull_degree (u : Z → O) : (scalarNull u).natDegree=(scalarValues u).card := by
  unfold scalarNull
  rw [natDegree_prod_of_monic (scalarValues u) (fun c => X-C c) (fun _ _ => monic_X_sub_C _)]
  simp

theorem scalarNull_zero (u : Z → O) (z : Z) : (scalarNull u).eval (u z)=0 := by
  unfold scalarNull
  rw [← coe_evalRingHom,map_prod]
  apply Finset.prod_eq_zero (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)
  simp

theorem scalar_bounded_power (u : Z → O) (n : ℕ) :
    ∃ c : Fin (scalarValues u).card → O,
      ∀ z, u z^n=∑ j : Fin (scalarValues u).card, c j*(u z)^j.val := by
  let Q := scalarNull u
  let R : O[X] := X^n %ₘ Q
  have hQ : Q.Monic := scalarNull_monic u
  have hd : Q.natDegree=(scalarValues u).card := scalarNull_degree u
  have hPos : 0<(scalarValues u).card := by
    obtain z := Classical.arbitrary Z
    exact Finset.card_pos.mpr ⟨u z,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩⟩
  have hne : Q≠1 := by
    intro h
    have h' := congrArg natDegree h
    rw [natDegree_one,hd] at h'
    omega
  have hr : R.natDegree<(scalarValues u).card := by
    rw [← hd]
    exact natDegree_modByMonic_lt (X^n) hQ hne
  refine ⟨fun j => R.coeff j,fun z => ?_⟩
  have he := congrArg (fun f : O[X] => f.eval (u z)) (modByMonic_add_div (X^n) hQ)
  change (R+Q*((X^n)/ₘ Q)).eval (u z)=(X^n).eval (u z) at he
  simp only [eval_add,eval_mul,eval_pow,eval_X] at he
  rw [show Q.eval (u z)=0 from scalarNull_zero u z,zero_mul,add_zero] at he
  rw [← he]
  have hR' := R.as_sum_range_C_mul_X_pow' hr
  conv_lhs => rw [hR']
  simp only [eval_finset_sum,eval_mul,eval_C,eval_pow,eval_X]
  exact (Fin.sum_univ_eq_sum_range (fun x => R.coeff x*(u z)^x) _).symm

abbrev ScalarRawIdx (u : Z → H → O) :=
  (i : H) → Fin (scalarValues (fun z => u z i)).card

def scalarRawMatrix (u : Z → H → O) : Matrix Z (ScalarRawIdx u) O :=
  Matrix.of fun z a => ∏ i : H, (u z i)^(a i).val

theorem scalarTensor_remainder (u : Z → H → O) (a : H → ℕ) :
    ∃ c : ScalarRawIdx u → O,
      ∀ z, (∏ i : H, u z i^a i)=∑ j : ScalarRawIdx u, c j*scalarRawMatrix u z j := by
  choose c hc using fun i : H => scalar_bounded_power (fun z => u z i) (a i)
  refine ⟨fun j => ∏ i : H, c i (j i),fun z => ?_⟩
  simp_rw [hc]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.prod_mul_distrib

theorem scalarRaw_contains_every_decoder (u : Z → H → O) (f : MvPolynomial H O) :
    evaluation u f ∈ matrixImage (scalarRawMatrix u) := by
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
    obtain ⟨k,hk⟩ := scalarTensor_remainder u a
    refine ⟨fun j => c*k j,?_⟩
    funext z
    change (∑ j : ScalarRawIdx u, scalarRawMatrix u z j*(c*k j)) =
      MvPolynomial.eval (u z) (MvPolynomial.monomial a c)
    change _=(MvPolynomial.eval₂Hom (RingHom.id O) (u z)) (MvPolynomial.monomial a c)
    rw [MvPolynomial.eval₂Hom_monomial,RingHom.id_apply,Finsupp.prod_pow,hk z,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  | add f g hf hg =>
    rw [map_add]
    exact Submodule.add_mem _ hf hg

theorem S4_finite_actual_matrix (u : Z → H → O) :
    scalarImage u = matrixImage (scalarRawMatrix u) := by
  ext z
  constructor
  · rintro ⟨f,rfl⟩
    exact scalarRaw_contains_every_decoder u f
  · rintro ⟨c,rfl⟩
    refine ⟨∑ j : ScalarRawIdx u, MvPolynomial.C (c j)*
      ∏ i : H, (MvPolynomial.X i)^(j i).val,?_⟩
    funext z
    change MvPolynomial.eval (u z) _ =
      ∑ j : ScalarRawIdx u, scalarRawMatrix u z j*c j
    simp only [map_sum,map_mul,MvPolynomial.eval_C,map_prod,map_pow,MvPolynomial.eval_X,
      scalarRawMatrix,Matrix.of_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

#print axioms scalarNull_degree
#print axioms scalarNull_zero
#print axioms scalar_bounded_power
#print axioms scalarTensor_remainder
#print axioms S4_finite_actual_matrix
end
end V8CapacityUnified.Scalar
