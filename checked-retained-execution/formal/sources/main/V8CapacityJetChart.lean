import V8CapacitySymbolic

/-! Every input of A^h is represented by the finite independent digit
chart, not just the polynomials that happen to have a supplied chart. -/
namespace V8CapacityJetChart
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityCRTJet V8CapacityTranslation V8CapacityFeatures V8CapacitySymbolic

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 850000

variable {O H : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable (π : O) (k : ℕ)
local notation "κ" => IsLocalRing.ResidueField O

def sourceInput (d : κ → O) (a : H → κ) (x : Digits H k → O) (i : H) : Jet O k :=
  AdjoinRoot.mk ((X:O[X])^k) (C (d (a i)) + shiftedPolynomial π k (asInput x i))

theorem receipt_reduce (d : κ → O) (a : H → κ) (x : Digits H k → O) (P : ℕ) (i : H) :
    reduceJet O π P k (sourceInput π k d a x i) = digitInput O π P k d a (asInput x) i := by
  unfold sourceInput
  rw [map_add,map_add]
  change reduceJet O π P k (constJet O k (d (a i)))+
    reduceJet O π P k (AdjoinRoot.mk ((X:O[X])^k) (shiftedPolynomial π k (asInput x i)))=_
  rw [reduceJet_const,source_reduce_mk,← finite_shift_is_mk]
  simp only [digitInput,digitShift,map_zero,zero_add]

def sourceTop (d : κ → O) (a : H → κ) (x : Digits H k → O) (F : MvPolynomial H (Jet O k)) : O :=
  coefficient O k (k-1)
    (MvPolynomial.eval₂Hom (RingHom.id _) (sourceInput π k d a x) F)

theorem native_top_reduce (d : κ → O) (a : H → κ) (x : Digits H k → O)
    (F : MvPolynomial H (Jet O k)) (P : ℕ) :
    coeffMod O π P (sourceTop π k d a x F) =
    coefficient (BaseMod O π P) k (k-1)
      (MvPolynomial.eval₂Hom (reduceJet O π P k) (digitInput O π P k d a (asInput x)) F) := by
  unfold sourceTop
  rw [← coefficient_reduce, MvPolynomial.map_eval₂Hom]
  simp only [RingHom.comp_id,receipt_reduce]

theorem source_surjective_single (hk : 0<k)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O)) (u : Jet O k) :
    ∃ a : κ, ∃ c : Fin k → O,
      AdjoinRoot.mk ((X:O[X])^k)
        (C (d a) + shiftedPolynomial π k (fun n => if h : n<k then c ⟨n,h⟩ else 0))=u := by
  obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective u
  let Q : O[X] := X^k
  let r := g %ₘ Q
  have hQ : Q.Monic := monic_X.pow k
  have hQ1 : Q≠1 := by
    intro he
    have h := congrArg natDegree he
    simp [Q] at h
    omega
  have hr : r.natDegree<k := by
    simpa [Q] using natDegree_modByMonic_lt g hQ hQ1
  have hm : AdjoinRoot.mk Q r=AdjoinRoot.mk Q g := by
    have e := congrArg (AdjoinRoot.mk Q) (modByMonic_add_div g hQ)
    simpa only [map_add,map_mul,AdjoinRoot.mk_self,zero_mul,add_zero,r] using e
  let a := IsLocalRing.residue O (r.coeff 0)
  have hzero : IsLocalRing.residue O (r.coeff 0 - d a)=0 := by
    rw [map_sub,hd]
    exact sub_self _
  have hdiv := (IsLocalRing.residue_eq_zero_iff _).mp hzero
  rw [hMax,Ideal.mem_span_singleton] at hdiv
  obtain ⟨v,hv⟩ := hdiv
  let c (n : Fin k) : O := if n.val=0 then v else r.coeff n.val
  refine ⟨a,c,?_⟩
  change AdjoinRoot.mk Q _ = AdjoinRoot.mk Q g
  rw [← hm]
  apply congrArg (AdjoinRoot.mk Q)
  unfold shiftedPolynomial
  dsimp only
  simp only [dif_pos hk]
  have he : d a+π*c ⟨0,hk⟩=r.coeff 0 := by
    have h : c ⟨0,hk⟩=v := by simp [c]
    rw [h,← hv]
    ring
  rw [← add_assoc,← map_add,he]
  have hs :
      X*(∑ j ∈ Finset.range (k-1), C (if h : j+1<k then c ⟨j+1,h⟩ else 0)*X^j) =
        ∑ j ∈ Finset.range (k-1), C (r.coeff (j+1))*X^(j+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [dif_pos (by have e:=Finset.mem_range.mp hj; omega),pow_succ]
    have h : j+1≠0 := by omega
    simp only [c,if_neg h]
    ac_rfl
  rw [hs]
  have hf := r.as_sum_range_C_mul_X_pow' hr
  rw [show k=(k-1).succ by omega,Finset.sum_range_succ'] at hf
  simpa only [pow_zero,mul_one,add_comm] using hf.symm

theorem source_chart_surjective (hk : 0<k)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O)) (u : H → Jet O k) :
    ∃ a : H → κ, ∃ x : Digits H k → O, sourceInput π k d a x=u := by
  choose a c hc using (fun i => source_surjective_single π k hk hMax d hd (u i))
  exact ⟨a,fun e => c e.1 e.2,funext hc⟩

#print axioms receipt_reduce
#print axioms native_top_reduce
#print axioms source_surjective_single
#print axioms source_chart_surjective
end
end V8CapacityJetChart

