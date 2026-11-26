import P5AlwaysSatOriginalTaylorRank
import P5AlwaysSatOriginalTaylorCaps
import P5AlwaysSatOriginalTaylorDirect
import P5MainBalanceM6DirectTop

/-! Source-identical finite specialization for both (M.7) MAIN branches.
Only the actual geometry and finite numeric hypothesis remain; no
coefficient, register, count, or parity truth premise is supplied. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6 Polynomial Real
open scoped BigOperators Classical Polynomial

variable {V Copy I B : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype Copy] [Fintype I] [DecidableEq I] [Nonempty I] [Fintype B] [LinearOrder B]
  [Nonempty B]
variable {E : Finset (V×V)} {T : Finset V}

section Direct
variable (L : SourceLayout (ClausePort E T) (Port E T) (CloneFactor E T) Copy I B)
variable (ho : L.placement.owner=portOwner E T) (hf : L.factor=portFactor E T)
local notation "D" => directChart L ho hf

set_option maxHeartbeats 9500000 in
theorem finite_direct_M5_M6 (G : MainIncidence.Layout E (D).mark (realCell L) 54)
    (hT : T.card≤Fintype.card V/4) (t : I→ℚ) (ht : Function.Injective t)
    (ht0 : ∀ i,t i≠0) (A R : ℕ) (ε : ℝ)
    (margins : FiniteMargins L (D).mark 54 G A R
      (fun _=>nominalOrder I (directDegree E T) R) 1 ε) :
    let k : I→ℕ := fun _=>nominalOrder I (directDegree E T) R
    let H := fun σ=>trimV 1 (actualH L (D).mark t (printedMix A R) (directRecipe L ho hf) σ)
    M5Witness L (D).mark 54 G.gamma G.symbols t k 1 H ∧
      HighWitness L (D).mark 54 G.gamma G.symbols t k 1 H ε := by
  dsimp only
  letI : Nonempty (Port E T) := ⟨bonusZeroPort E T⟩
  have hDegree : ((∑ f,directBase L ho hf f)+0*(1-1))*R<
      ∑ _i : I,nominalOrder I (directDegree E T) R := by
    rw [zero_mul,add_zero,direct_nominal L ho hf]
    exact nominal_grid_strict (I:=I) (directDegree E T) R
  obtain ⟨out,hOut,hParity⟩ := direct_terminal_witness L ho hf t (printedMix A R)
  exact finite_source_both L (D).mark 54 G t ht ht0 A R _ 1 ε
    (directRecipe L ho hf) (directBase L ho hf) 0 (direct_grade L ho hf) hDegree margins
    (literal_clone_variable_range E T G.regular hT).2 out hOut hParity
end Direct

#print axioms finite_direct_M5_M6
end Paper5.AlwaysSatOriginal.Physical.Taylor