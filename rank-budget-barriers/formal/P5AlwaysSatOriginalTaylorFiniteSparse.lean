import P5AlwaysSatOriginalTaylorRank
import P5AlwaysSatOriginalTaylorCaps
import P5AlwaysSatOriginalTaylorSparse
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

section Sparse
variable (L : SourceLayout (SparsePort E T) (Port E T) (SparseFactor E T) Copy I B)
variable (ho : L.placement.owner=sparseOwner E T) (hf : L.factor=sparseFactor E T)
local notation "D" => sparseChart L ho hf

set_option maxHeartbeats 9500000 in
theorem finite_sparse_M5_M6 (G : MainIncidence.Layout E (D).mark (realCell L) 54)
    (hT : T.card≤Fintype.card V/4) (t : I→ℚ) (ht : Function.Injective t)
    (ht0 : ∀ i,t i≠0) (A R : ℕ) (ε : ℝ)
    (margins : FiniteMargins L (D).mark 54 G A R
      (fun _=>nominalOrder I (sparseDegree E T) R) (mainN E T+1) ε) :
    let ell := mainN E T+1
    let k : I→ℕ := fun _=>nominalOrder I (sparseDegree E T) R
    let H := fun σ=>trimV ell (actualH L (D).mark t (printedMix A R)
      ((sparseInput L ho hf).compile ell) σ)
    M5Witness L (D).mark 54 G.gamma G.symbols t k ell H ∧
      HighWitness L (D).mark 54 G.gamma G.symbols t k ell H ε := by
  dsimp only
  letI : Nonempty (Port E T) := ⟨bonusZeroPort E T⟩
  let ell := mainN E T+1
  have hDegree : ((∑ f,(sparseInput L ho hf).base f)+6*(ell-1))*R<
      ∑ _i : I,nominalOrder I (sparseDegree E T) R := by
    rw [sparse_nominal_base L ho hf,show ell-1=mainN E T by simp [ell]]
    exact nominal_grid_strict (I:=I) (sparseDegree E T) R
  obtain ⟨out,hOut,hParity⟩ := sparse_terminal_witness L ho hf ell
    (Nat.succ_pos _) t (printedMix A R)
  exact finite_source_both L (D).mark 54 G t ht ht0 A R _ ell ε
    ((sparseInput L ho hf).compile ell) (sparseInput L ho hf).base 6
    ((sparseInput L ho hf).graded ell) hDegree margins
    (literal_clone_variable_range E T G.regular hT).2 out hOut hParity
end Sparse

#print axioms finite_sparse_M5_M6
end Paper5.AlwaysSatOriginal.Physical.Taylor