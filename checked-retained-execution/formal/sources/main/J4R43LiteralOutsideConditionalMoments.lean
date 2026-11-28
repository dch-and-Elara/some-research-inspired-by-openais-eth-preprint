import J4R43LiteralOutsideConditional

/-! The only conditional moments consulted by the derandomizer
are restrictions to one closed star or the union of two stars. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

variable {U : Type*} [Fintype U] [DecidableEq U]

def required (e : U) : U→Bool := fun q=>decide (q=e)

def rawIndicator (B : U→Finset U) (e : U) (w : U→Bool) : ℚ :=
  if prescribe (B e) (required e) w then 1 else 0

def oneMoment (a : U→Option Bool) (B : U→Finset U) (e : U) : ℚ :=
  localMass a (B e) (required e)

def sameRequest (B : U→Finset U) (e f : U) : Prop :=
  ∀ q∈B e ∩ B f,required e q=required f q

def bothRequest (B : U→Finset U) (e f : U) (q : U) : Bool :=
  if q∈B e then required e q else required f q

def twoMoment (a : U→Option Bool) (B : U→Finset U) (e f : U) : ℚ :=
  if sameRequest B e f then localMass a (B e∪B f) (bothRequest B e f) else 0

theorem requests_consistent (B : U→Finset U) (e f : U) (w : U→Bool)
    (one : prescribe (B e) (required e) w) (two : prescribe (B f) (required f) w) :
    sameRequest B e f :=
  fun q h=>(one q (Finset.mem_inter.mp h).1).symm.trans (two q (Finset.mem_inter.mp h).2)

theorem both_request_exact (B : U→Finset U) (e f : U) (w : U→Bool) (same : sameRequest B e f) :
    prescribe (B e∪B f) (bothRequest B e f) w ↔
      prescribe (B e) (required e) w ∧ prescribe (B f) (required f) w := by
  constructor
  · intro h
    constructor
    · intro q hq
      simpa [bothRequest,hq] using h q (Finset.mem_union_left _ hq)
    · intro q hq
      have H := h q (Finset.mem_union_right _ hq)
      by_cases L : q∈B e
      · simp only [bothRequest,if_pos L] at H
        exact H.trans (same q (Finset.mem_inter.mpr ⟨L,hq⟩))
      · simpa [bothRequest,L] using H
  · rintro ⟨l,r⟩ q hq
    by_cases ok : q∈B e
    · simpa [bothRequest,ok] using l q ok
    · have qr := (Finset.mem_union.mp hq).resolve_left ok
      simpa [bothRequest,ok] using r q qr

theorem one_moment_exact (a : U→Option Bool) (B : U→Finset U) (e : U) :
    conditionalExpected a (rawIndicator B e)=oneMoment a B e :=
  conditional_pattern_exact a _ _

theorem two_moment_exact (a : U→Option Bool) (B : U→Finset U) (e f : U) :
    conditionalExpected a (fun w=>rawIndicator B e w*rawIndicator B f w)=twoMoment a B e f := by
  by_cases ok : sameRequest B e f
  · rw [twoMoment,if_pos ok,←conditional_pattern_exact]
    apply congrArg (conditionalExpected a)
    funext w
    unfold rawIndicator
    rw [both_request_exact B e f w ok]
    by_cases H : prescribe (B e) (required e) w <;>
      by_cases J : prescribe (B f) (required f) w <;> simp [H,J]
  · rw [twoMoment,if_neg ok]
    unfold conditionalExpected
    refine Finset.sum_eq_zero fun w _=>?_
    unfold rawIndicator
    by_cases H : prescribe (B e) (required e) w
    · have J : ¬prescribe (B f) (required f) w := fun J=>ok (requests_consistent B e f w H J)
      simp [H,J]
    · simp [H]

theorem one_star_scan_bound (B : U→Finset U) (D : ℕ) (short : ∀ e,(B e).card≤D) (e : U) :
    (B e).card≤D := short e

theorem two_star_scan_bound (B : U→Finset U) (D : ℕ) (short : ∀ e,(B e).card≤D) (e f : U) :
    (B e∪B f).card≤2*D ∧ (B e∩B f).card≤D := by
  constructor
  · exact (Finset.card_union_le _ _).trans (by have h:=Nat.add_le_add (short e) (short f); omega)
  · exact (Finset.card_le_card Finset.inter_subset_left).trans (short e)

#print axioms requests_consistent
#print axioms both_request_exact
#print axioms one_moment_exact
#print axioms two_moment_exact
#print axioms two_star_scan_bound
end
end J4R43LiteralOutside

