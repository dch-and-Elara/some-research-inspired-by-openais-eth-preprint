import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.FinRange
import Mathlib.Tactic
import Std.Sat.CNF.Basic

/-! Literal signed-unit input to the rational CNF proposition.  The
normalization and no-split tests describe the operations in source lines
3577–3581 and 3647–3671; they do not describe the alternative D dispatch. -/
namespace Paper5.NativeEntry

abbrev F₂ := ZMod 2
abbrev Lit (n : ℕ) := Fin n × Bool

def unitClause {n : ℕ} (sgn : Fin n → Bool) (v : Fin n) :
    Std.Sat.CNF.Clause (Fin n) := [(v,sgn v)]

def signedUnits {n : ℕ} (sgn : Fin n → Bool) : Std.Sat.CNF (Fin n) :=
  (List.finRange n).map (unitClause sgn)

theorem length_units {n : ℕ} (sgn : Fin n → Bool) :
    (signedUnits sgn).length=n := by simp [signedUnits]

theorem sat_units {n : ℕ} (sgn x : Fin n → Bool) :
    (signedUnits sgn).Sat x ↔ x=sgn := by
  simp [signedUnits,unitClause,Std.Sat.CNF.sat_def,Std.Sat.CNF.eval,List.all_eq_true,
    funext_iff]

noncomputable def modelCount {n : ℕ} (f : Std.Sat.CNF (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Fin n→Bool => f.Sat x).card

theorem count_units {n : ℕ} (sgn : Fin n → Bool) :
    modelCount (signedUnits sgn)=1 := by
  classical
  unfold modelCount
  have he : (Finset.univ.filter fun x : Fin n→Bool => (signedUnits sgn).Sat x)
      ={sgn} := by ext x; simp [sat_units]
  rw [he,Finset.card_singleton]

theorem every_declared_variable_occurs {n : ℕ} (sgn : Fin n → Bool) (v : Fin n) :
    ∃ C ∈ signedUnits sgn, ∃ val, (v,val)∈ C :=
  ⟨unitClause sgn v,by simp [signedUnits],sgn v,by simp [unitClause]⟩

theorem normalization_duplicate_free {n : ℕ} (sgn : Fin n → Bool) :
    (signedUnits sgn).Nodup ∧
    (∀ C ∈ signedUnits sgn,C.Nodup) := by
  have hinj : Function.Injective (unitClause sgn) := by
    intro u v h
    simpa [unitClause] using congrArg (List.map Prod.fst) h
  exact ⟨(List.nodup_finRange n).map hinj,by simp [signedUnits,unitClause]⟩

theorem normalization_width_tautology {n : ℕ} (sgn : Fin n → Bool)
    {C : Std.Sat.CNF.Clause (Fin n)} (hC : C∈signedUnits sgn) :
    C.length=1 ∧ ¬ ∃ v, (v,true)∈C ∧ (v,false)∈C := by
  simp only [signedUnits,List.mem_map] at hC
  obtain ⟨v,_,rfl⟩ := hC
  simp [unitClause]

theorem normalization_no_proper_subsumption {n : ℕ} (sgn : Fin n → Bool)
    {C D : Std.Sat.CNF.Clause (Fin n)} (hC : C∈signedUnits sgn)
    (hD : D∈signedUnits sgn) (hCD : ∀ l, l∈C → l∈D) : C=D := by
  simp only [signedUnits,List.mem_map] at hC hD
  obtain ⟨u,_,rfl⟩ := hC
  obtain ⟨v,_,rfl⟩ := hD
  have h := hCD (u,sgn u) (by simp [unitClause])
  simpa [unitClause] using h

theorem no_sparsification_seed {n : ℕ} (sgn : Fin n → Bool)
    {C : Std.Sat.CNF.Clause (Fin n)} (hC : C∈signedUnits sgn)
    (H : Finset (Lit n)) (hne : H.Nonempty)
    (hHC : ∀ l∈H,l∈C) : H=C.toFinset := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp (show C ∈ (List.finRange n).map (unitClause sgn) from hC)
  exact Finset.eq_of_subset_of_card_le (fun l hl=> by simpa using hHC l hl)
    (by simpa [unitClause] using Finset.one_le_card.mpr hne)

def asBit : Bool → F₂
  | false => 0
  | true => 1

theorem asBit_injective : Function.Injective asBit := by
  decide

noncomputable def bitEquiv : Bool ≃ F₂ :=
  Equiv.ofBijective asBit ⟨asBit_injective,by
    have h : Fintype.card Bool=Fintype.card F₂ := by simp
    exact (Fintype.bijective_iff_injective_and_card asBit).mpr ⟨asBit_injective,h⟩ |>.2⟩

/-- The source clause-violation polynomial at the single variable. -/
def unitViolation (s x : F₂) : F₂ := if s=1 then 1+x else x

theorem unit_violation_formula (s x : Bool) :
    unitViolation (asBit s) (asBit x)=asBit x+asBit s := by
  cases s <;> cases x <;> decide

theorem unit_violation_bit (s x : Bool) :
    asBit (x != s)=unitViolation (asBit s) (asBit x) := by
  cases s <;> cases x <;> decide

#print axioms length_units
#print axioms sat_units
#print axioms count_units
#print axioms every_declared_variable_occurs
#print axioms normalization_duplicate_free
#print axioms normalization_width_tautology
#print axioms normalization_no_proper_subsumption
#print axioms no_sparsification_seed
#print axioms asBit_injective
#print axioms unit_violation_formula
#print axioms unit_violation_bit
end Paper5.NativeEntry