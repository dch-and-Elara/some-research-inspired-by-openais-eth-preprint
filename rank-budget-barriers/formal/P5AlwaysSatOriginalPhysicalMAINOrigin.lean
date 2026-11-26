import P5AlwaysSatOriginalPhysicalSparsePoly

/-! Actual counting semantics of the undeformed rational clause factors
and of the Boolean sparse equation system. This is not a receipt for
the deformed Taylor table or a recursive run. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
variable {V K : Type*} [Fintype V] [CommRing K] [Nontrivial K]
variable (E : Finset (V×V)) (T : Finset V)

noncomputable def satisfactionFactor (s : V→Bool) (f : CloneFactor E T) :
    MvPolynomial (Port E T) K := 1-violation (clonedClause E T s f)

theorem satisfaction_factor_truth (s : V→Bool) (f : CloneFactor E T) (x : Port E T→Bool) :
    MvPolynomial.eval (bitValue ∘ x) (satisfactionFactor (K:=K) E T s f) =
      if (clonedClause E T s f).eval x then 1 else 0 := by
  rw [satisfactionFactor,map_sub,map_one,violation_on_bits]
  cases (clonedClause E T s f).eval x <;> simp

noncomputable def originCount (s : V→Bool) : K :=
  ∑ x : Port E T→Bool,∏ f : CloneFactor E T,
    MvPolynomial.eval (bitValue ∘ x) (satisfactionFactor (K:=K) E T s f)

theorem source_origin_cloned_exact (s : V→Bool) :
    originCount (K:=K) E T s=(PinnedCNF.modelCount (cloneCNF E T s):K) := by
  unfold originCount
  have hf (x : Port E T→Bool) :
      (∏ f : CloneFactor E T,
        MvPolynomial.eval (bitValue ∘ x) (satisfactionFactor (K:=K) E T s f)) =
        if (cloneCNF E T s).Sat x then (1:K) else 0 := by
    simp only [satisfaction_factor_truth]
    by_cases hs : (cloneCNF E T s).Sat x
    · rw [if_pos hs]
      have hs' := (all_cloned_clauses E T s x).mp hs
      simp [hs']
    · rw [if_neg hs,all_cloned_clauses] at *
      obtain ⟨f,hf⟩ := not_forall.mp hs
      apply Finset.prod_eq_zero (Finset.mem_univ f)
      rw [if_neg hf]
  simp_rw [hf]
  have ht := Finset.sum_filter (s:=(Finset.univ : Finset (Port E T→Bool)))
    (p:=fun x=>(cloneCNF E T s).Sat x) (f:=fun _=>(1:K))
  rw [←ht]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  unfold PinnedCNF.modelCount
  congr 1
  apply congrArg Finset.card
  ext a
  simp [Std.Sat.CNF.sat_def]

theorem source_origin_M7 (s : V→Bool) :
    originCount (K:=K) E T s =
      ((2^(1+∑ v∈T,if s v then (1:ℕ) else 0)+
          PinnedCNF.modelCount (PinnedCNF.formula E s):ℕ):K) := by
  rw [source_origin_cloned_exact,cloned_display_M7]

omit [CommRing K] [Nontrivial K] in
theorem sparse_origin_old_cover (s : V→Bool) :
    originCount (K:=ZMod 2) E T s =
      (PinnedCNF.modelCount (PinnedCNF.formula E s):ZMod 2) := by
  rw [source_origin_cloned_exact]
  rw [←cloned_count_parity E T s, ZMod.natCast_mod]

#print axioms satisfaction_factor_truth
#print axioms source_origin_cloned_exact
#print axioms source_origin_M7
#print axioms sparse_origin_old_cover
end Paper5.AlwaysSatOriginal.Physical