import J6R11IntegralStep

/-! A single printed mode profile of the actual contraction, not just the
sum over all profiles. Oversized profiles vanish on both sides. -/
namespace J9R15FrozenErasureProjection
open scoped Classical BigOperators Polynomial
open J6ActiveAllocation J6ActiveProfile J6ActiveTargetSum J6BlockFactor
open J6FixedProfile J6ChildIdentity J6SourceMoment J6LiteralCoeff
open J6R10GroupAssembly J6R11RowFormula

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

section Generic
variable {I M G K R : Type*} [Fintype I] [Fintype M] [Fintype G] [Fintype K] [CommRing R]

def allocationExponent (x : I → Option M) : M →₀ ℕ :=
  ∑ r, LiteralPortCompiler.exponent (x r)

theorem allocation_count (x : I → Option M) (m : M) :
    allocationExponent x m = count x m := by
  have he (r : I) : LiteralPortCompiler.exponent (x r) = J6PacketCoefficientBridge.exponent (x r) := by
    cases x r <;> rfl
  unfold allocationExponent
  simp only [he, J6PacketCoefficientBridge.exponent_sum]

theorem allocation_match (x : I → Option M) (b : Profile I M) :
    allocationExponent x=profileFinsupp b ↔ profile x=b := by
  constructor
  · intro h
    funext m
    apply Fin.ext
    simpa only [profileFinsupp,Finsupp.equivFunOnFinite_symm_apply_toFun,allocation_count] using
      congrArg (fun v : M →₀ ℕ => v m) h
  · intro h
    ext m
    have hm := congrArg (fun v : Profile I M => (v m).val) h
    simpa only [profileFinsupp,Finsupp.equivFunOnFinite_symm_apply_toFun,allocation_count] using hm

theorem fixed_row_sum (w : M → ℕ) (f : I → Option M → R)
    (block : I → K) (target : M → K) (hzero : ∀ i m, block i≠target m → f i (some m)=0)
    (L : M → R) (b : Profile I M) :
    (∑ x : I → Option M, if profile x=b then ∏ i, scaled w (J6SourceMoment.insert f L) i (x i) else 0) =
      (∏ m, L m^(b m).val)*∏ k, targetCoeff w f block target b k := by
  have hbase : (∑ x : I → Option M, if Legal block target x ∧
      (∀ m, count (fun j : {i : I // block i=target m} => x j.val) m=(b m).val)
      then ∏ i, scaled w f i (x i) else 0) = ∏ k, targetCoeff w f block target b k := by
    simp only [← all_tests block target b]
    simpa only [targetCoeff,Finset.prod_const_one,one_mul] using
      (sum_with_block_test block (test block target b) (scaled w f) (fun _ _ => (1:R)))
  rw [← hbase,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hL : Legal block target x
  · have he := J6TargetProfile.profile_is_local x block target hL b
    simp only [hL,true_and,← he]
    by_cases hx : profile x=b
    · rw [if_pos hx,if_pos hx]
      have hf (i : I) : scaled w (J6SourceMoment.insert f L) i (x i) =
          scaled w f i (x i) * (x i).elim' 1 L := by simp [scaled,J6SourceMoment.insert,mul_assoc]
      simp only [hf,Finset.prod_mul_distrib,moment_of_choices]
      have hc (m : M) : count x m=(b m).val := congrArg (fun v : Profile I M => (v m).val) hx
      simp only [hc,mul_comm]
    · rw [if_neg hx,if_neg hx,mul_zero]
  · have hz := incorrect_erase w (J6SourceMoment.insert f L) block target
      (fun i m h => by simp [J6SourceMoment.insert,hzero i m h]) x hL
    simp only [hz,ite_self,hL,false_and,if_false,mul_zero]

variable {V : G → Type*} [∀ g, Fintype (V g)] [∀ g, Inhabited (V g)]

def groupedProjection (w : M → ℕ) (block : I → G×K) (source : M → G×K)
    (row : ∀ i, V (block i).1 → Option M → R)
    (old : ∀ g,V g → R) (L : ∀ m,V (source m).1 → R)
    (β : M →₀ ℕ) : R :=
  ∑ x : ∀ g,V g, (∏ g, old g (x g)) *
    ∑ α : I → Option M, if allocationExponent α=β then
      ∏ i, scaled w (J6SourceMoment.insert (fun i => row i (x (block i).1))
        (fun m => L m (x (source m).1))) i (α i)
    else 0

/-- For one request, exactly the printed product. This equality precedes
the finite menu cut, and so also identifies an unbounded multiplicity
request as structurally zero rather than hiding it in a total sum. -/
theorem exact_projection
    (w : M → ℕ) (block : I → G×K) (target source : M → G×K)
    (row : ∀ i,V (block i).1 → Option M → R)
    (old : ∀ g,V g → R) (L : ∀ m,V (source m).1 → R)
    (bit : ∀ g,V g → I → Bool) (base : ∀ g,V g → I → R) (cross : ∀ g,V g → I → M → R)
    (hzero : ∀ i m v, block i≠target m → row i v (some m)=0)
    (h0 : ∀ g (y : V g) i (e : (block i).1=g),
      scaled w (fun _ m => row i (e.symm ▸ y) m) i none = LiteralPortCompiler.affine (bit g y i) (base g y i))
    (hm : ∀ g (y : V g) i (e : (block i).1=g) m,
      scaled w (fun _ o => row i (e.symm ▸ y) o) i (some m) =
        LiteralPortCompiler.slope (bit g y i)*cross g y i m)
    (β : M →₀ ℕ) :
    groupedProjection w block source row old L β =
      ∏ g, canonicalChild block target source old L bit base cross β g := by
  classical
  by_cases hB : ∀ m, β m≤Fintype.card I
  · let b : Profile I M := fun m => ⟨β m,Nat.lt_succ_of_le (hB m)⟩
    have hb : β=profileFinsupp b := by ext m; simp [profileFinsupp,b]
    rw [hb]
    unfold groupedProjection
    have hcore := J6ChildGroup.contract_grouped Prod.fst (Prod.fst ∘ source) old
      (localizedCoeff w block target Prod.fst row b) (fun m v => L m v ^ (b m).val)
    refine Eq.trans ?_ (hcore.trans ?_)
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [allocation_match]
      rw [fixed_row_sum w _ block target (fun i m => hzero i m _) (fun m => L m (x (source m).1)) b]
      simp only [coefficient_is_local,mul_assoc,Function.comp_apply]
    · refine Finset.prod_congr rfl (fun g _ => ?_)
      convert exact_one_child w block target source row old L bit base cross hzero h0 hm b g using 1
      apply Finset.sum_congr rfl
      intro y _
      have hc : (∏ m : rows (Prod.fst ∘ source) g, L m.val (@Eq.rec G g (fun u _ => V u) y ((Prod.fst ∘ source) m.val) m.property.symm) ^ (b m.val).val) =
          ∏ m : rows (Prod.fst ∘ source) g, L m.val (cast (congrArg V m.property.symm) y) ^ (b m.val).val := by
        apply Finset.prod_congr rfl
        rintro ⟨m,e⟩ _
        change (source m).1=g at e
        subst g
        rfl
      have hd : (∏ k : rows (Prod.fst : G×K → G) g, localizedCoeff w block target Prod.fst row b
          k.val (@Eq.rec G g (fun u _ => V u) y k.val.1 k.property.symm)) = ∏ k : rows (Prod.fst : G×K → G) g,
            localizedCoeff w block target Prod.fst row b k.val (cast (congrArg V k.property.symm) y) := by
        apply Finset.prod_congr rfl
        rintro ⟨⟨g',k⟩,e⟩ _
        change g'=g at e
        subst g
        rfl
      rw [hc,hd]
  · push_neg at hB
    obtain ⟨m,hm'⟩ := hB
    have hz : groupedProjection w block source row old L β=0 := by
      unfold groupedProjection
      refine Finset.sum_eq_zero (fun x _ => mul_eq_zero_of_right _ ?_)
      refine Finset.sum_eq_zero (fun α _ => if_neg ?_)
      intro hα
      have he : count α m=β m := (allocation_count α m).symm.trans (congrArg (fun b : M →₀ ℕ => b m) hα)
      exact (not_lt_of_ge (Finset.card_filter_le _ _)) (he.symm ▸ hm')
    rw [hz]
    exact (J6NoOversizedChild.oversized_child_product_zero target source
      (J6R10PacketAssembly.actualRows block) old bit base cross _ β ⟨m,hm'⟩).symm

end Generic
#print axioms allocation_count
#print axioms allocation_match
#print axioms fixed_row_sum
#print axioms exact_projection
end
end J9R15FrozenErasureProjection
