import P5PrecisionOptProfiles

/-! Exact finite optimization over every legal node order. In
particular order zero is selectable independently at each node. The
finite maximum is semantic (no claim that enumerating it is fast). -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

abbrev OrderChoices (M u : ℕ) :=
  ∀ t : Paper5.P3.rootNodes u, Fin (taper u (sourceH M u) (level t.val)+1)

def choiceProfile (M u : ℕ) (x : OrderChoices M u) : Profile u :=
  fun t => (x t).val

theorem every_choice_legal (M u : ℕ) (x : OrderChoices M u) :
    admissibleOrders M u (choiceProfile M u x) := fun t => Nat.le_of_lt_succ (x t).isLt

theorem every_legal_choice (M u : ℕ) (q : Profile u) (h : admissibleOrders M u q) :
    ∃ x : OrderChoices M u, choiceProfile M u x=q :=
  ⟨fun t => ⟨q t,Nat.lt_succ_of_le (h t)⟩,rfl⟩

noncomputable def profileCap (M u p : ℕ) (q : Profile u) : ℕ :=
  if ha : (Paper5.P3.activeNodes q).Nonempty then
    (Paper5.P3.largestBound q (Paper5.P3.printedDegree u M)
      (fun t => Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val)
      (fun t => Paper5.P3.nativeLoss (2*u) t.val)
      (Paper5.P3.nativeCarrierVal Subtype.val q) p ha).toNat
  else 0

noncomputable def exactRootOpt (M u p : ℕ) : ℕ :=
    (Finset.univ : Finset (OrderChoices M u)).sup (fun x => profileCap M u p (choiceProfile M u x))

variable {K : Type*} [Field K] [CharZero K]

def RootCertified (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (M u p : ℕ) (q : Profile u) (b : ℕ) : Prop :=
  Paper5.P3.degreeAdmissible q (Paper5.P3.printedDegree u M) b ∧
    Paper5.P3.ActualCertified O (fun t : Paper5.P3.rootNodes u => Paper5.P3.nativeCenter (2*u) t.val)
      q b
      (fun s t => Paper5.P3.nativeDifference_integral_inverses O hn2 (2*u) s.val t.val
        (Finset.mem_filter.mp s.property).1 (Finset.mem_filter.mp t.property).1)
      (fun t => (↑(Paper5.P3.twoUnit K^Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val):K))
      (↑(Paper5.P3.twoUnit K^(p:ℤ)):K)

theorem fixed_profile_cap_exact (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (M u p : ℕ) (q : Profile u) {b : ℕ} (hb : 0<b) :
    RootCertified O hn2 M u p q b ↔ b≤profileCap M u p q := by
  by_cases ha : (Paper5.P3.activeNodes q).Nonempty
  · unfold RootCertified profileCap
    rw [dif_pos ha,Paper5.P3.printed_root_window_p2 O hn2 u M p b q ha]
    omega
  · have he : Paper5.P3.activeNodes q=∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    unfold RootCertified profileCap
    rw [dif_neg ha]
    constructor
    · intro h
      exact False.elim ((Paper5.P3.no_window_of_empty_active q (Paper5.P3.printedDegree u M) b he) h.1)
    · intro h
      omega

theorem finite_optimum_exact (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (M u p : ℕ) {b : ℕ} (hb : 0<b) :
    (∃ q : Profile u, admissibleOrders M u q ∧ RootCertified O hn2 M u p q b) ↔
      b≤exactRootOpt M u p := by
  constructor
  · rintro ⟨q,hq,hcert⟩
    obtain ⟨x,rfl⟩ := every_legal_choice M u q hq
    have H := (fixed_profile_cap_exact O hn2 M u p (choiceProfile M u x) hb).mp hcert
    unfold exactRootOpt
    exact H.trans (Finset.le_sup (f:=fun x : OrderChoices M u => profileCap M u p (choiceProfile M u x))
      (Finset.mem_univ x))
  · intro H
    have hex : ∃ x : OrderChoices M u,b≤profileCap M u p (choiceProfile M u x) := by
      by_contra h
      have hb' : exactRootOpt M u p ≤ b-1 := by
        apply Finset.sup_le
        intro x _
        have H := Nat.lt_of_not_ge (fun hh => h ⟨x,hh⟩)
        omega
      omega
    obtain ⟨x,hx⟩ := hex
    exact ⟨choiceProfile M u x,every_choice_legal M u x,
      (fixed_profile_cap_exact O hn2 M u p (choiceProfile M u x) hb).mpr hx⟩

#print axioms every_legal_choice
#print axioms fixed_profile_cap_exact
#print axioms finite_optimum_exact
end Paper5.PrecisionOpt
