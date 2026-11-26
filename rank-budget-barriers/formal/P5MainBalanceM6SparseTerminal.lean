import P5MainBalanceM6SparseTests
import P5MainBalanceM6SparseGuards

/-! Both actual sparse witnesses. Neither final integer/parity nor local
V-lift equality is a hypothesis of these source-specific theorems. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical

variable {V Copy I B : Type*} [LinearOrder B]
variable {G : Finset (V×V)} {left right : G→Fin 4}

set_option maxHeartbeats 9000000 in
theorem uncloned_compiled_anchor (L : UChart (Copy:=Copy) (I:=I) (B:=B) G)
    (ell : ℕ) (f : UFactor G)
    (s : {v : V // signedOwner L.physical (uMark G) v=f}→Bool) (x : V→Bool) :
    atAnchorFactor L.physical (uMark G) ((uSource L).compile ell) f s x =
      (sparseEntry ell (uncloned_local G L.physical (uMark G) L.pin_owner f s x)).map
        (Int.castRingHom ℚ) := by
  cases f with
  | inl f =>
    let y := uncloned_local G L.physical (uMark G) L.pin_owner (.inl f) s x
    have hy : y.isSome=true := by cases f <;> rfl
    obtain ⟨z,hz⟩ : ∃ z,y=some z := by
      cases h : y with
      | none => simp [h] at hy
      | some z => exact ⟨z,rfl⟩
    change _=(sparseEntry ell y).map _
    rw [hz]
    exact (uSource L).anchor_compiled_of_evenTest ell (.inl f) s x z rfl
      (uSource_anchor_literal L _ _ _ _ hz)
  | inr f =>
    change _=(sparseEntry ell none).map _
    rw [sparseEntry,Polynomial.map_one]
    exact (uSource L).anchor_compiled_neutral ell (.inr f) s x rfl

set_option maxHeartbeats 9000000 in
theorem cloned_compiled_anchor (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right)
    (ell : ℕ) (f : CFactor G)
    (s : {v : V // signedOwner L.physical (cMark G) v=f}→Bool) (x : V×Fin 4→Bool) :
    atAnchorFactor L.physical (cMark G) ((cSource L).compile ell) f s x =
      (sparseEntry ell (cloned_local G left right L.physical (cMark G) L.pin_owner f s x)).map
        (Int.castRingHom ℚ) := by
  cases f with
  | inl f =>
    let y := cloned_local G left right L.physical (cMark G) L.pin_owner (.inl f) s x
    have hy : y.isSome=true := by rcases f with v|e|⟨v,i⟩ <;> rfl
    obtain ⟨z,hz⟩ : ∃ z,y=some z := by
      cases h : y with
      | none => simp [h] at hy
      | some z => exact ⟨z,rfl⟩
    change _=(sparseEntry ell y).map _
    rw [hz]
    exact (cSource L).anchor_compiled_of_evenTest ell (.inl f) s x z rfl
      (cSource_anchor_literal L _ _ _ _ hz)
  | inr f =>
    change _=(sparseEntry ell none).map _
    rw [sparseEntry,Polynomial.map_one]
    exact (cSource L).anchor_compiled_neutral ell (.inr f) s x rfl

variable [Fintype V] [DecidableEq V] [Fintype Copy] [Fintype I] [Fintype B]

theorem uncloned_compiled_terminal (L : UChart (Copy:=Copy) (I:=I) (B:=B) G)
    (ell : ℕ) (he : 0<ell) (t : I→ℚ) (M : Mix Copy I B) :
    ∃ out : (V→Bool)→ℤ,
      (∀ σ,(out σ:ℚ)=
        retainedOrigin ell (actualH L.physical (uMark G) t M ((uSource L).compile ell) σ)) ∧
      (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula G σ):ZMod 2)) :=
  uncloned_terminal_from_lift G L.physical (uMark G) L.pin_owner t M
    ((uSource L).compile ell) ell he (uncloned_compiled_anchor L ell)

theorem cloned_compiled_terminal (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right)
    (ell : ℕ) (he : 0<ell) (t : I→ℚ) (M : Mix Copy I B) :
    ∃ out : (V→Bool)→ℤ,
      (∀ σ,(out σ:ℚ)=
        retainedOrigin ell (actualH L.physical (cMark G) t M ((cSource L).compile ell) σ)) ∧
      (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula G σ):ZMod 2)) :=
  cloned_terminal_from_lift G left right L.physical (cMark G) L.pin_owner t M
    ((cSource L).compile ell) ell he (cloned_compiled_anchor L ell)

private theorem sum_test_base {F S : Type*} [Fintype F] [Fintype S] :
    (∑ f : F⊕S,testBase f)=2*Fintype.card F := by
  rw [Fintype.sum_sum_type]
  simp only [testBase,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,mul_zero,add_zero]
  exact Nat.mul_comm _ _

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem uncloned_compiled_nominal (L : UChart (Copy:=Copy) (I:=I) (B:=B) G)
    (reg : ∀ v,GraphCutMoments.degree G v=3) :
    (∑ f : UFactor G,(uSource L).base f)+4*((Fintype.card V+1)-1)=9*Fintype.card V := by
  rw [uSource_base,sum_test_base]
  have h := (uncloned_nominal_guards G reg).2.2.1
  unfold sparseNominal at h
  omega

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem cloned_compiled_nominal (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right)
    (reg : ∀ v,GraphCutMoments.degree G v=3) :
    (∑ f : CFactor G,(cSource L).base f)+4*((Fintype.card (V×Fin 4)+1)-1)=29*Fintype.card V := by
  rw [cSource_base,sum_test_base]
  calc
    _ = sparseNominal (Fintype.card (V×Fin 4)) (Fintype.card (Direct.Factor G)) := by
      unfold sparseNominal
      omega
    _ = _ := (cloned_nominal_guards G reg).2.2.2.1

#print axioms uncloned_compiled_anchor
#print axioms cloned_compiled_anchor
#print axioms uncloned_compiled_terminal
#print axioms cloned_compiled_terminal
#print axioms uncloned_compiled_nominal
#print axioms cloned_compiled_nominal
end P5MainBalance.M6.Sparse
