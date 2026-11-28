import F5R60AmbientRequests

/-! Restrict a selected ambient set to the original occurrences, and
extend it back by disabling every extra vertex. The exact original
binary and triple requests survive both directions. -/
namespace F5R60.Ambient
set_option autoImplicit false
open scoped Classical
noncomputable section

variable {C V : Type} {n : ℕ}
variable (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
variable (B : SimpleGraph (Fin n))

def selected (x : Vertices n → Bool) (v : F5R59.Vertex S) : Prop :=
  x (originalVertex S key v)=true

def extend (I : F5R59.Vertex S → Prop) : Vertices n → Bool
  | .inl i => decide (∃ v : F5R59.Vertex S, key v=i ∧ I v)
  | .inr _ => false

def RespectsGate (x : Vertices n → Bool) : Prop :=
  ∀ v, x v=true → available S key v=true

theorem extension_respects_gate (I : F5R59.Vertex S → Prop) :
    RespectsGate S key (extend S key I) := by
  intro v h
  cases v with
  | inl i =>
    have hs : ∃ v : F5R59.Vertex S, key v=i ∧ I v := by simpa [extend] using h
    obtain ⟨a,ha,_hi⟩ := hs
    exact (available_on_old S key i).2 ⟨a,ha⟩
  | inr i =>
    simp [extend] at h

theorem restrict_extension (I : F5R59.Vertex S → Prop) :
    selected S key (extend S key I)=I := by
  funext v
  apply propext
  change (extend S key I (.inl (key v))=true) ↔ I v
  simp only [extend,decide_eq_true_eq]
  constructor
  · rintro ⟨a,eq,ha⟩
    exact key.injective eq ▸ ha
  · intro hv
    exact ⟨v,rfl,hv⟩

theorem extension_restores_allowed_choices (x : Vertices n → Bool) (gate : RespectsGate S key x) :
    extend S key (selected S key x)=x := by
  funext v
  cases v with
  | inl i =>
    cases hi : x (.inl i) with
    | false =>
      apply Bool.eq_false_iff.mpr
      intro ht
      have hs : ∃ v : F5R59.Vertex S, key v=i ∧ selected S key x v := by
        simpa [extend] using ht
      obtain ⟨a,eq,ha⟩ := hs
      change x (.inl (key a))=true at ha
      rw [eq,hi] at ha
      cases ha
    | true =>
      have h := (available_on_old S key i).1 (gate _ hi)
      obtain ⟨a,eq⟩ := h
      have ha : selected S key x a := by change x (.inl (key a))=true; rw [eq,hi]
      simp only [extend,decide_eq_true_eq]
      exact ⟨a,eq,ha⟩
  | inr i =>
    cases hi : x (.inr i) with
    | false => rfl
    | true =>
      have h := gate (.inr i) hi
      change false=true at h
      cases h

theorem conflicts_are_exactly_old_independence (x : Vertices n → Bool) (gate : RespectsGate S key x) :
    (∀ e : Edge (paddedH S key) B,
      ¬(x (ends (paddedH S key) B e false)=true ∧ x (ends (paddedH S key) B e true)=true)) ↔
    F5R59.isIndependent S (selected S key x) := by
  constructor
  · intro cf u v hu hv h
    let e := originalConflictEdge S key B h
    apply cf e
    have endsHere := original_conflict_endpoints S key B h
    change (ends (paddedH S key) B e false=originalVertex S key u ∧
      ends (paddedH S key) B e true=originalVertex S key v) ∨
      (ends (paddedH S key) B e false=originalVertex S key v ∧
      ends (paddedH S key) B e true=originalVertex S key u) at endsHere
    rcases endsHere with ⟨l,r⟩ | ⟨l,r⟩
    · rw [l,r]; exact ⟨hu,hv⟩
    · rw [l,r]; exact ⟨hv,hu⟩
  · intro indep e ⟨hu,hv⟩
    rcases e with ((e | e) | j)
    · change x (.inl e.val.1)=true at hu
      change x (.inl e.val.2)=true at hv
      have hSource := (SimpleGraph.map_adj key (conflictGraph S) e.val.1 e.val.2).1 e.property.2
      obtain ⟨i,j,h,hi,hj⟩ := hSource
      apply indep i j _ _ h
      · change x (.inl (key i))=true
        exact hi.symm ▸ hu
      · change x (.inl (key j))=true
        exact hj.symm ▸ hv
    · change x (.inr e.val.1)=true at hu
      exact Bool.false_ne_true (gate (.inr e.val.1) hu)
    · change x (.inr j)=true at hv
      exact Bool.false_ne_true (gate (.inr j) hv)

theorem actual_binary_hit_iff (x : Vertices n → Bool) (c : TwoClause S) :
    let e := binaryEdge S key B c
    (x (ends (paddedH S key) B e false)=true ∨ x (ends (paddedH S key) B e true)=true) ↔
      selected S key x (F5R59.atTwo S c.val c.property 0) ∨
      selected S key x (F5R59.atTwo S c.val c.property 1) := by
  dsimp only
  have h := original_conflict_endpoints S key B (F5R59.atTwo_edge S c.val c.property)
  change (ends (paddedH S key) B (binaryEdge S key B c) false =
        originalVertex S key (F5R59.atTwo S c.val c.property 0) ∧
      ends (paddedH S key) B (binaryEdge S key B c) true =
        originalVertex S key (F5R59.atTwo S c.val c.property 1)) ∨
    (ends (paddedH S key) B (binaryEdge S key B c) false =
        originalVertex S key (F5R59.atTwo S c.val c.property 1) ∧
      ends (paddedH S key) B (binaryEdge S key B c) true =
        originalVertex S key (F5R59.atTwo S c.val c.property 0)) at h
  rcases h with ⟨a,b⟩ | ⟨a,b⟩
  · rw [a,b]; rfl
  · rw [a,b]; exact or_comm

theorem ambient_allowed_exact (x : Vertices n → Bool) :
    F5R60.Allowed (requestGraph S key B) x ↔
      RespectsGate S key x ∧ F5R59.isIndependent S (selected S key x) ∧
        F5R59.hitsPrintedRequests S (selected S key x) := by
  constructor
  · intro h
    have gate : RespectsGate S key x := h.1
    refine ⟨gate,(conflicts_are_exactly_old_independence S key B x gate).1 h.2.1,?_⟩
    constructor
    · intro c w
      let pair : TwoClause S := ⟨c,w⟩
      let e := binaryEdge S key B pair
      have active : edgeActive S key B e=true :=
        (edge_active_iff_original_binary S key B e).2 ⟨pair,rfl⟩
      exact (actual_binary_hit_iff S key B x pair).1 (h.2.2.1 e active)
    · intro c w
      exact h.2.2.2 ⟨c,w⟩ rfl
  · rintro ⟨gate,indep,hits⟩
    refine ⟨gate,(conflicts_are_exactly_old_independence S key B x gate).2 indep,?_,?_⟩
    · intro e active
      have hActive : edgeActive S key B e=true := active
      obtain ⟨c,hc⟩ := (edge_active_iff_original_binary S key B e).1 hActive
      have h := (actual_binary_hit_iff S key B x c).2 (hits.1 c.val c.property)
      change x (ends (paddedH S key) B e false)=true ∨ x (ends (paddedH S key) B e true)=true
      exact hc ▸ h
    · intro c _active
      exact hits.2 c.val c.property

/-- Exact one-to-one preservation of the allowed literal selections,
not of satisfying assignments of the pre-conflict SAT instance. -/
def allowed_choice_equiv :
    {x : Vertices n → Bool // F5R60.Allowed (requestGraph S key B) x} ≃
      {I : F5R59.Vertex S → Prop // F5R59.isIndependent S I ∧ F5R59.hitsPrintedRequests S I} where
  toFun x := ⟨selected S key x.val,((ambient_allowed_exact S key B x.val).1 x.property).2⟩
  invFun I := ⟨extend S key I.val,(ambient_allowed_exact S key B _).2
    ⟨extension_respects_gate S key I.val,by rw [restrict_extension]; exact I.property⟩⟩
  left_inv x := Subtype.ext (extension_restores_allowed_choices S key x.val x.property.1)
  right_inv I := Subtype.ext (restrict_extension S key I.val)

theorem actual_ambient_requests_iff (widths : ∀ c, S.width c=2 ∨ S.width c=3) :
    (∃ x : Vertices n → Bool, F5R60.Allowed (requestGraph S key B) x) ↔
    ∃ a : V → Bool, F5R59.satisfies S a := by
  rw [F5R59.decision_equivalence_for_printed_requests S widths]
  constructor
  · rintro ⟨x,hx⟩
    let Q := allowed_choice_equiv S key B ⟨x,hx⟩
    exact ⟨Q.val,Q.property⟩
  · rintro ⟨I,hI⟩
    let Q := (allowed_choice_equiv S key B).symm ⟨I,hI⟩
    exact ⟨Q.val,Q.property⟩

#print axioms extension_respects_gate
#print axioms restrict_extension
#print axioms extension_restores_allowed_choices
#print axioms conflicts_are_exactly_old_independence
#print axioms actual_binary_hit_iff
#print axioms ambient_allowed_exact
#print axioms allowed_choice_equiv
#print axioms actual_ambient_requests_iff
end
end F5R60.Ambient
