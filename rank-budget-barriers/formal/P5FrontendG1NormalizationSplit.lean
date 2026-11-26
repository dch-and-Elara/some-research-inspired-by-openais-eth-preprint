import P5FrontendG1NormalizationGuard
import GraphCutMoments

/-! Exact no-split certificate for the rational sparsification root on the
guarded G1 source. Edge degrees are for the actual old graph, with each
stored edge counted once at each distinct endpoint. -/
namespace Paper5.FrontendG1.Normalization
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def widthTwoUsing {W : Type*} [DecidableEq W] (F : Family W) (w : W) :
    Family W := by
  classical
  exact F.filter fun C => C.card=2 ∧ ((w,true)∈C ∨ (w,false)∈C)

def incidentEdges (E : Finset (V×V)) (v : V) : Finset (V×V) :=
  E.filter fun e => e.1=v ∨ e.2=v

omit [Fintype V] in
theorem incident_le_degree (E : Finset (V×V)) (v : V) :
    (incidentEdges E v).card ≤ GraphCutMoments.degree E v := by
  have hh : incidentEdges E v = (E.filter fun e=>e.1=v) ∪ (E.filter fun e=>e.2=v) := by
    ext e
    simp only [incidentEdges,Finset.mem_filter,Finset.mem_union]
    tauto
  rw [hh,GraphCutMoments.degree]
  exact Finset.card_union_le _ _

theorem width_two_x_le (E : Finset (V×V)) (sgn : V→Bool) (v : V) :
    (widthTwoUsing (parsed (guardedFormula E sgn)) (.inl v)).card ≤
      1+GraphCutMoments.degree E v := by
  classical
  let L : Family (GuardVar V) := {guardSet E sgn (.inr (.inl v))}
  let R := (incidentEdges E v).image (positiveEdge (Sum.inl : V→GuardVar V))
  have hInc : widthTwoUsing (parsed (guardedFormula E sgn)) (.inl v) ⊆ L∪R := by
    intro C hC
    obtain ⟨hm,hTwo,hUses⟩ := Finset.mem_filter.mp hC
    obtain ⟨i,rfl⟩ := (guarded_parsed_mem E sgn C).mp hm
    rcases i with u|(u|e)
    · simp at hTwo
    · have hv : v=u := by
        cases hs : sgn u <;> simpa [hs] using hUses
      subst u
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self _))
    · have hu : e.val.1=v ∨ e.val.2=v := by
        simpa [positiveEdge,eq_comm] using hUses
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨e.val,Finset.mem_filter.mpr ⟨e.property,hu⟩,(guardSet_edge E sgn e).symm⟩))
  calc
    _ ≤ (L∪R).card := Finset.card_le_card hInc
    _ ≤ L.card+R.card := Finset.card_union_le _ _
    _ ≤ 1+GraphCutMoments.degree E v := by
      have hh : R.card ≤ GraphCutMoments.degree E v :=
        Finset.card_image_le.trans (incident_le_degree E v)
      simpa [L] using (Nat.add_le_add_left hh 1)

theorem width_two_z_le (E : Finset (V×V)) (sgn : V→Bool) (v : V) :
    (widthTwoUsing (parsed (guardedFormula E sgn)) (.inr v)).card ≤ 1 := by
  classical
  let L : Family (GuardVar V) := {guardSet E sgn (.inr (.inl v))}
  have hInc : widthTwoUsing (parsed (guardedFormula E sgn)) (.inr v) ⊆ L := by
    intro C hC
    obtain ⟨hm,hTwo,hUses⟩ := Finset.mem_filter.mp hC
    obtain ⟨i,rfl⟩ := (guarded_parsed_mem E sgn C).mp hm
    rcases i with u|(u|e)
    · simp at hTwo
    · have hv : v=u := by simpa using hUses
      subst u
      exact Finset.mem_singleton_self _
    · simp [positiveEdge] at hUses
  calc
    _ ≤ L.card := Finset.card_le_card hInc
    _ = 1 := Finset.card_singleton _

theorem guarded_width_two_le_four (E : Finset (V×V)) (sgn : V→Bool)
    (hD : ∀v, GraphCutMoments.degree E v≤3) (w : GuardVar V) :
    (widthTwoUsing (parsed (guardedFormula E sgn)) w).card≤4 := by
  rcases w with v|v
  · exact (width_two_x_le E sgn v).trans (Nat.add_le_add_left (hD v) 1)
  · exact (width_two_z_le E sgn v).trans (by decide)

theorem guarded_shared_two_le_four (E : Finset (V×V)) (sgn : V→Bool)
    (hD : ∀v, GraphCutMoments.degree E v≤3) (H : ClauseSet (GuardVar V))
    (hH : H.Nonempty) :
    degShared (parsed (guardedFormula E sgn)) 2 H ≤ 4 := by
  classical
  obtain ⟨⟨w,b⟩,hw⟩ := hH
  unfold degShared
  apply (Finset.card_le_card (t:=widthTwoUsing (parsed (guardedFormula E sgn)) w) ?_).trans
    (guarded_width_two_le_four E sgn hD w)
  intro C hC
  obtain ⟨hF,hTwo,hSub⟩ := Finset.mem_filter.mp hC
  refine Finset.mem_filter.mpr ⟨hF,hTwo,?_⟩
  have HH := hSub hw
  cases b with
  | false => exact Or.inr HH
  | true => exact Or.inl HH

theorem guarded_no_eligible_split (E : Finset (V×V)) (hS : OrientedSimple E)
    (sgn : V→Bool) (hD : ∀v, GraphCutMoments.degree E v≤3)
    {M : ℕ} (hM : 4<M) : ¬SplitEligible M (parsed (guardedFormula E sgn)) := by
  rintro ⟨C,hC,H,hne,hSub,hBad⟩
  have hlt := Finset.card_lt_card hSub
  have hH := Finset.one_le_card.mpr hne
  have hCC := guarded_literal_width E hS sgn hC
  have h2 : C.card=2 := by omega
  have hExp : C.card-H.card=1 := by omega
  rw [hExp,pow_one,h2] at hBad
  exact (not_le_of_gt hM) (hBad.trans (guarded_shared_two_le_four E sgn hD H hne))

theorem guard_every_variable_occurs (E : Finset (V×V)) (sgn : V→Bool)
    (w : GuardVar V) :
    ∃ C ∈ parsed (guardedFormula E sgn), ∃ b, (w,b)∈C := by
  rcases w with v|v
  · refine ⟨guardSet E sgn (.inr (.inl v)), (guarded_parsed_mem E sgn _).mpr ⟨_,rfl⟩,
      sgn v,?_⟩
    simp
  · refine ⟨guardSet E sgn (.inl v), (guarded_parsed_mem E sgn _).mpr ⟨_,rfl⟩,true,?_⟩
    simp

omit [DecidableEq V] in
theorem guarded_variable_card :
    Fintype.card (GuardVar V)=2*Fintype.card V := by simp [GuardVar,Nat.two_mul]

theorem guarded_cubic_clause_card (E : Finset (V×V)) (hS : OrientedSimple E)
    (sgn : V→Bool) (hD : ∀v,GraphCutMoments.degree E v=3) :
    2*(parsed (guardedFormula E sgn)).card=7*Fintype.card V := by
  have hc := GraphCutMoments.regular_edge_count E 3 hD
  rw [guarded_parsed_card E hS sgn,guarded_length]
  omega

theorem guarded_single_unchanged_leaf [Nonempty V] (E : Finset (V×V))
    (hS : OrientedSimple E) (sgn : V→Bool)
    (hD : ∀v, GraphCutMoments.degree E v≤3) {M : ℕ} (hM : 4<M) :
    sourceRoot M (parsed (guardedFormula E sgn)) =
      .leaf (parsed (guardedFormula E sgn)) := by
  apply sourceRoot_unsplit M _ (normalize_actual_guard E hS sgn)
  · intro h0
    obtain h1|h2 := guarded_literal_width E hS sgn h0 <;> simp at *
  · obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨guardSet E sgn (.inl v),(guarded_parsed_mem E sgn _).mpr ⟨_,rfl⟩⟩
  · exact guarded_no_eligible_split E hS sgn hD hM

#print axioms incident_le_degree
#print axioms width_two_x_le
#print axioms width_two_z_le
#print axioms guarded_width_two_le_four
#print axioms guarded_shared_two_le_four
#print axioms guarded_no_eligible_split
#print axioms guard_every_variable_occurs
#print axioms guarded_variable_card
#print axioms guarded_cubic_clause_card
#print axioms guarded_single_unchanged_leaf
end Paper5.FrontendG1.Normalization