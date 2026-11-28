import J4R43LiteralOutsideSeating
import IndependentThinning

/-! Literal fair marking on the original incidence network after deleting
the designated edge's closed neighborhood. Each retained mark is a
matching edge, and the pinned edge itself is never a random choice. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open J6R10Repack P11FullPacking
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3500000

variable {E A B : Type} [Fintype E]
variable (N : Network E A B)

def adjacent (e e' : E) : Prop := N.row e=N.row e' ∨ N.col e=N.col e'

theorem adjacent_symm {e e' : E} (h : adjacent N e e') : adjacent N e' e :=
  h.elim (fun e=>Or.inl e.symm) (fun e=>Or.inr e.symm)

abbrev Eligible (pin : E) := {e : E//¬adjacent N pin e}

def close (e : E) : Finset E := Finset.univ.filter (adjacent N e)

def block (pin : E) (e : Eligible N pin) : Finset (Eligible N pin) :=
  Finset.univ.filter (fun q=>adjacent N e.val q.val)

theorem block_contains (pin : E) (e : Eligible N pin) : e∈block N pin e :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩

theorem block_symmetric (pin : E) (e q : Eligible N pin) (h : q∈block N pin e) :
    e∈block N pin q :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, adjacent_symm N (Finset.mem_filter.mp h).2⟩

private theorem filter_card_of_base {X Y : Type*} [Fintype X] (allowed : X→Prop)
    [DecidablePred allowed] (f : X→Y) (u : Y) :
    (Finset.univ.filter (fun q : Subtype allowed=>f q.val=u)).card≤Nat.card {q : X//f q=u} := by
  let S := (Finset.univ : Finset (Subtype allowed)).filter (fun q=>f q.val=u)
  let w : ↥S→{q : X//f q=u} := fun q=>⟨q.val.val,(Finset.mem_filter.mp q.prop).2⟩
  have inj : Function.Injective w := by
    intro x y he
    have eq : x.val.val=y.val.val := congrArg (fun z : {q : X//f q=u}=>z.val) he
    exact Subtype.ext (Subtype.ext eq)
  simpa only [Nat.card_eq_fintype_card (α:=↥S),Fintype.card_coe] using Nat.card_le_card_of_injective w inj

private theorem union_bound_with_self {X : Type*} [DecidableEq X] (A B : Finset X) (e : X)
    (hA : e∈A) (hB : e∈B) (d : ℕ) (a : A.card≤d) (b : B.card≤d) :
    (A∪B).card≤2*d-1 := by
  have hi : 0<(A∩B).card := Finset.card_pos.mpr ⟨e,Finset.mem_inter.mpr ⟨hA,hB⟩⟩
  have u := Finset.card_union_add_card_inter A B
  omega

variable (degree : ℕ)
variable (dr : ∀ x : A,Nat.card {e : E//N.row e=x}≤degree)
variable (dc : ∀ x : B,Nat.card {e : E//N.col e=x}≤degree)

include dr dc in
theorem literal_closed_count (e : E) : (close N e).card≤2*degree-1 := by
  let R := Finset.univ.filter (fun q : E=>N.row q=N.row e)
  let C := Finset.univ.filter (fun q : E=>N.col q=N.col e)
  have he : close N e=R∪C := by ext q; simp [R,C,close,adjacent,eq_comm]
  rw [he]
  have hr : R.card≤degree := by
    simpa [R,Nat.card_eq_fintype_card,Fintype.card_subtype] using dr (N.row e)
  have hc : C.card≤degree := by
    simpa [C,Nat.card_eq_fintype_card,Fintype.card_subtype] using dc (N.col e)
  exact union_bound_with_self R C e (by simp [R]) (by simp [C]) degree hr hc

include dr dc in
theorem literal_block_count (pin : E) (e : Eligible N pin) :
    (block N pin e).card≤2*degree-1 := by
  let R := Finset.univ.filter (fun q : Eligible N pin=>N.row q.val=N.row e.val)
  let C := Finset.univ.filter (fun q : Eligible N pin=>N.col q.val=N.col e.val)
  have he : block N pin e=R∪C := by ext q; simp [R,C,block,adjacent,eq_comm]
  rw [he]
  have hr : R.card≤degree := by
    unfold R
    exact (filter_card_of_base (fun q=>¬adjacent N pin q) N.row (N.row e.val)).trans (dr _)
  have hc : C.card≤degree := by
    unfold C
    exact (filter_card_of_base (fun q=>¬adjacent N pin q) N.col (N.col e.val)).trans (dc _)
  exact union_bound_with_self R C e (by simp [R]) (by simp [C]) degree hr hc

variable (pin : E)

def Keep (marks : Eligible N pin→Bool) (e : Eligible N pin) : Prop :=
  ∀ q∈block N pin e, marks q=decide (q=e)

def kept (marks : Eligible N pin→Bool) (e : E) : Prop :=
  e=pin ∨ ∃ q : Eligible N pin, q.val=e ∧ Keep N pin marks q

theorem pin_is_kept (marks : Eligible N pin→Bool) : kept N pin marks pin := Or.inl rfl

theorem kept_raw_neighbors_equal (marks : Eligible N pin→Bool)
    {e e' : E} (k : kept N pin marks e) (k' : kept N pin marks e')
    (h : adjacent N e e') : e=e' := by
  rcases k with rfl|⟨v,rfl,hv⟩
  · rcases k' with rfl|⟨v,rfl,hv⟩
    · rfl
    · exact False.elim (v.prop h)
  · rcases k' with rfl|⟨w,rfl,hw⟩
    · exact False.elim (v.prop (adjacent_symm N h))
    by_contra ne
    have diff : w≠v := fun e=>ne (congrArg Subtype.val e.symm)
    have w0 := hv w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    have w1 := hw w (block_contains N pin w)
    simp [diff] at w0
    simp at w1
    exact Bool.false_ne_true (w0.symm.trans w1)

def actual_marking_band_supply {G : Type} [Fintype G] [LinearOrder G] {a : ℕ}
    (P : PhysicalPacking N a G) (h : ℕ) (hc : 0<P.copies)
    (marks : Eligible N pin→Bool)
    (quota : ∀ c : Cell (Fin a) G,
      2*h*P.copies≤Nat.card {w : InputCell P c // kept N pin marks w.val}) :
    BandSupply P h pin where
  good := kept N pin marks
  row := fun _ _ k k' e=>kept_raw_neighbors_equal N pin marks k k' (Or.inl e)
  col := fun _ _ k k' e=>kept_raw_neighbors_equal N pin marks k k' (Or.inr e)
  pin_good := pin_is_kept N pin marks
  hasCopy := hc
  quota := quota

#print axioms adjacent_symm
#print axioms block_contains
#print axioms block_symmetric
#print axioms literal_closed_count
#print axioms literal_block_count
#print axioms pin_is_kept
#print axioms kept_raw_neighbors_equal
#print axioms actual_marking_band_supply
end
end J4R43LiteralOutside

