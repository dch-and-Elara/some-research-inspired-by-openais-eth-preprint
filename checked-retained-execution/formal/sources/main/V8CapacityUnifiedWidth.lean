import V8CapacityUnifiedActive

/-! Literal matrix separation width of any attainable-column module
in U1. Both the genuine quotient and exact width use the original row
index type. The lower bound allows factors outside the attainable image. -/
namespace V8CapacityUnified
open scoped Classical BigOperators
open V8CapacityCRTJet V8CapacitySmith V8CapacityWidthUpper V8CapacityWidthLower Module

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O X I Y : Type*} [CommRing O] [IsDomain O] [Fintype X] [Fintype I] [Fintype Y]
variable {π : O} {E : Submodule O (X → O)} {n : ℕ}
variable (p : ℕ) (S : Powered π E I n) (L : ℕ)

local notation "B" => BaseMod O π p
local notation "Act" => Active S (L+p)

def factors (π : O) (p : ℕ) (v : Y → X → BaseMod O π p) (d : ℕ) : Prop :=
  ∃ a : Matrix X (Fin d) (BaseMod O π p), ∃ b : Matrix (Fin d) Y (BaseMod O π p),
    Matrix.of (fun x y => v y x)=a*b

/-- Every attainable matrix factors over the actual output ring. -/
theorem U_width_upper (hπ : π≠0) (v : Y → X → B)
    (h : matrixRead (E:=E) p L v) :
    factors π p v (Fintype.card Act) := by
  choose c hc using fun y => generator_sum p S L hπ (v y) (h y)
  let e := Fintype.equivFin Act
  refine ⟨Matrix.of (fun x i => generator p S L hπ (e.symm i) x),
    Matrix.of (fun i y => c y (e.symm i)),?_⟩
  ext x y
  have hv := congrFun (hc y) x
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hv
  change v y x=∑ i : Fin (Fintype.card Act), generator p S L hπ (e.symm i) x*c y (e.symm i)
  have he := e.symm.sum_comp (fun i : Act => generator p S L hπ i x*c y i)
  exact hv.trans ((Finset.sum_congr rfl (fun _ _ => mul_comm _ _)).trans he.symm)

variable [IsLocalRing O] [IsPrincipalIdealRing O]

/-- A genuine uniformizer plus finite ambient rows constructs U2's chart
for any actual submodule, with no pre-supplied coordinate array. -/
def U2_chart (π : O) (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (E : Submodule O (X → O)) : Σ n, Powered π E X n :=
  exists_powered π hMax (Pi.basisFun O X) E

theorem U_width_witness_lower (hπ : π≠0) (hp : 0<p) (hz : IsLocalRing.residue O π=0)
    (d : ℕ) (hf : factors π p (generator p S L hπ) d) : Fintype.card Act≤d := by
  obtain ⟨A,C,hA⟩ := hf
  have hc (i : Act) : generator p S L hπ i∈LinearMap.range A.mulVecLin := by
    refine ⟨fun j => C j i,?_⟩
    funext x
    have h := congrArg (fun M : Matrix X Act B => M x i) hA
    exact h.symm
  have hi (w : (i : Act) → BaseMod O π (activeLength p S L i)) :
      ∃ z, A.mulVecLin z=activeEmbed p S L hπ w := by
    change activeEmbed p S L hπ w∈LinearMap.range A.mulVecLin
    have hv : activeEmbed p S L hπ w∈attainable π L p E :=
      ((activeIso p S L hπ) w).property
    obtain ⟨c,he⟩ := generator_sum p S L hπ _ hv
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ (c i) (hc i))
  have h := residue_embedded_cyclic_width π hz (activeLength p S L)
    (activeLength_pos p S L hp) p (activeEmbed p S L hπ)
      (activeEmbed_inj p S L hπ) A.mulVecLin hi
  simpa using h

theorem U_width_exact (hπ : π≠0) (hp : 0<p)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) :
    ∃ v : Act → X → B, matrixRead (E:=E) p L v ∧
      IsLeast {d : ℕ | factors π p v d} (Fintype.card Act) := by
  have hz : IsLocalRing.residue O π=0 := by
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    rw [hMax,Ideal.mem_span_singleton]
  let v := generator p S L hπ
  have hv : matrixRead (E:=E) p L v := generator_attains p S L hπ
  refine ⟨v,hv,U_width_upper p S L hπ v hv,?_⟩
  intro d hd
  exact U_width_witness_lower p S L hπ hp hz d hd

/-- Upper and lower also apply literally to the permitted source numerators,
assuming only the exact readout image equality, not arbitrary free values. -/
theorem U_width_real_receivers {G : Type*} (hπ : π≠0) (hp : 0<p)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (read : G → X → O) (hE : Set.range read=↑E) :
    ∃ recv : Act → G, ∃ v : Act → X → O,
      (∀ y x, π^(L+p)∣read (recv y) x-π^L*v y x) ∧
      IsLeast {d : ℕ | factors π p (fun y => residueRows π p (v y)) d} (Fintype.card Act) := by
  obtain ⟨w,hw,hm⟩ := U_width_exact p S L hπ hp hMax
  choose v hv using fun y => residueRows_surj π p (w y)
  have hr : (fun y => residueRows π p (v y))=w := funext hv
  have hs : matrixRead (E:=E) p L (fun y => residueRows π p (v y)) := by rw [hr]; exact hw
  obtain ⟨recv,hrecv⟩ := (U1_receiver_columns π L p E read hE v).mpr hs
  refine ⟨recv,v,hrecv,?_⟩
  rw [hr]
  exact hm

#print axioms U_width_upper
#print axioms U2_chart
#print axioms U_width_witness_lower
#print axioms U_width_exact
#print axioms U_width_real_receivers
end
end V8CapacityUnified
