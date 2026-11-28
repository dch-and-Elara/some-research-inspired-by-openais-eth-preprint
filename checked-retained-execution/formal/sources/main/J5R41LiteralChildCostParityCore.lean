import J45ParityNative

/-! A parity table has Boolean *indices* even when the old
weights are in a larger receiving ring. No claim that the actual
extension and nilpotent coefficients are scalars in F₂. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators
open JointContraction
noncomputable section
set_option linter.unusedSectionVars false

variable {D A B M R : Type*} [Fintype D] [DecidableEq D] [Fintype A] [Fintype B] [Fintype M]
  [CommRing R] {P : A→Type*} {Q : B→Type*} [∀ a,Fintype (P a)] [∀ b,Fintype (Q b)]

def weightedParityTable (s : List B) (ports : M→Sigma Q)
    (wire : ∀ a,P a→Option M) (unit : R)
    (tabA : ∀ a,(P a→Bool)→R) (tabB : ∀ b,(Q b→Bool)→R)
    (inc : ∀ b,(Q b→Bool)→J45Parity.Bits D) (T : Finset D) : R :=
  ∑ w : M→Bool, rowValue wire unit tabA w *
    J45Parity.groupRun (fun b z => if agrees ports w b z then tabB b z else 0) inc s (J45Parity.vector T)

theorem weighted_parity_menu (s : List B) (hs : s.Nodup) (full : s.toFinset=Finset.univ)
    (ports : M→Sigma Q) (wire : ∀ a,P a→Option M) (unit : R)
    (tabA : ∀ a,(P a→Bool)→R) (tabB : ∀ b,(Q b→Bool)→R)
    (inc : ∀ b,(Q b→Bool)→J45Parity.Bits D) (embed : ZMod 2 →+* R) (S : Finset D) :
    J45Parity.run (weightedParityTable s ports wire unit tabA tabB inc)
        (Finset.univ : Finset D).toList S =
     ∑ x : (∀ b,Q b→Bool), ∑ y : (∀ a,P a→Bool),
      ((∏ a,tabA a (y a)) * ∏ a,∏ p,
        literal (y a p) (wiredInput unit (matchedBits ports x) (wire a p))) *
      ((∏ b,tabB b (x b)) * (∏ d∈S,embed ((∑ b,inc b (x b)) d))) := by
  rw [J45Parity.all_moments, joint_moment_contraction ports wire unit tabA tabB inc (fun x => ∏ d∈S,embed (x d))]
  let A' := weightedParityTable s ports wire unit tabA tabB inc
  let md := fun x : J45Parity.Bits D=>∏ d∈S,embed (x d)
  have hconvert : (∑ T : Finset D,if S⊆T then A' T else 0)=
      ∑ T : Finset D,A' T*md (J45Parity.vector T) := by
    refine Finset.sum_congr rfl fun T _=>?_
    have m : md (J45Parity.vector T)=(if S⊆T then 1 else 0) := by
      dsimp only [md]
      rw [←map_prod,J45Parity.monomial_in_mask]
      split_ifs <;> simp
    rw [m]
    split_ifs <;> simp
  rw [hconvert]
  simp only [A',weightedParityTable,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [←Finset.mul_sum]
  congr 1
  have hsum : (∑ T : Finset D,J45Parity.groupRun (fun b z => if agrees ports w b z then tabB b z else 0)
      inc s (J45Parity.vector T) * md (J45Parity.vector T)) =
      ∑ x : J45Parity.Bits D,J45Parity.groupRun (fun b z => if agrees ports w b z then tabB b z else 0)
      inc s x * md x :=
    Fintype.sum_equiv J45Parity.maskChart _ _ (fun _=>rfl)
  rw [hsum,J45Parity.group_readout_exact s hs full]

#print axioms weighted_parity_menu
end
end J5R41LiteralChildCost

