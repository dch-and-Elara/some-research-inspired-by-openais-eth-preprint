import J7R10Ports
import Mathlib.Data.Fintype.BigOperators

/-!
# Every actual physical half-wire appears exactly once at the old side

Count the occurrences of each half address across all old-node local
positions and prove they are exactly one. This supplies the old row
chart required by J6 Plant, with no assumed layout bijection.
-/

open Std.Sat
open scoped BigOperators

namespace J7R10Counts
open J7R9Compiler J7R9Subdivision J7R9EqualityTree J7R9DirectedTree J7R10Ports
variable {V : Type*} [DecidableEq V]

private theorem marked_mem {A : Type*} (ps : List A) (a : A) (b : Bool) :
    (a,b) ∈ ps.map (fun w => (w,true)) ↔ a ∈ ps ∧ b=true := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := List.mem_map.mp h
    rcases Prod.ext_iff.mp he with ⟨rfl,hb⟩
    exact ⟨hq,hb.symm⟩
  · rintro ⟨ha,rfl⟩
    exact List.mem_map.mpr ⟨a,ha,rfl⟩

theorem external_nodup (F : CNF V) (v : V) : (external F v).Nodup := by
  unfold external occurrences
  exact (Finset.nodup_toList _).map Sum.inl_injective

theorem internal_nodup (F : CNF V) (v : V) : (internal F v).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro j k h
  have hh := Sum.inr.inj h
  cases hh
  rfl

private theorem marked_nodup (F : CNF V) (v : V) :
    ((external F v).map (fun w => (w,true))).Nodup :=
  (external_nodup F v).map (fun _ _ h => congrArg Prod.fst h)

private theorem internal_not_external (F : CNF V) (v : V) (o : Occurrence F) :
    (Sum.inl o : Wire F) ∉ internal F v := by
  intro h
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  cases hi

private theorem external_not_internal (F : CNF V) (v : V) (i : Internal F) :
    (Sum.inr i : Wire F) ∉ external F v := by
  intro h
  obtain ⟨x,_hx,he⟩ := List.mem_map.mp h
  cases he

/-- Pin all counts to the canonical equality test from DecidableEq,
rather than to a type-specific BEq found by notation elaboration. -/
def countByEq {A : Type*} [DecidableEq A] (l : List A) (x : A) : ℕ :=
  @List.count A instBEqOfDecidableEq x l

private theorem physical_multiplicity (F : CNF V) (v : V) (q : Half F) :
    countByEq (physicalVar F v).flatten q =
      countByEq ((external F v).map (fun jw => (jw,true))) q+
      countByEq (internal F v) q.1 := by
  unfold physicalVar
  have hh := half_multiplicity ((external F v).map (fun j => (j,true))) (internal F v)
    (by simpa only [List.length_map] using treeShape F v) q
  simpa only [countByEq,List.count_eq_countP,Bool.beq_eq_decide_eq] using hh

private theorem count_ite {A : Type*} [DecidableEq A] (l : List A) (x : A) (h : l.Nodup) :
    countByEq l x = if x ∈ l then 1 else 0 :=
  List.count_eq_of_nodup h

/-- On an external wire only its true half can meet a variable tree.
Each half of an internal wire meets its owning variable tree once. -/
theorem variable_count_external (F : CNF V) (v : V) (o : Occurrence F) (b : Bool) :
    countByEq (physicalVar F v).flatten ((Sum.inl o : Wire F),b) =
      if (literal F o).1=v ∧ b=true then 1 else 0 := by
  rw [physical_multiplicity, count_ite _ _ (marked_nodup F v),
    count_ite _ _ (internal_nodup F v),if_neg (internal_not_external F v o)]
  simp only [marked_mem,external_member,add_zero]

theorem variable_count_internal (F : CNF V) (v : V) (i : Internal F) (b : Bool) :
    countByEq (physicalVar F v).flatten ((Sum.inr i : Wire F),b) =
      if i.1=v then 1 else 0 := by
  have he : ((Sum.inr i : Wire F),b) ∉ (external F v).map (fun w => (w,true)) :=
    fun h => external_not_internal F v i ((marked_mem _ _ _).mp h).1
  rw [physical_multiplicity, count_ite _ _ (marked_nodup F v),
    if_neg he,count_ite _ _ (internal_nodup F v),zero_add]
  simp only [internal_member]

variable [Fintype V]

def clauseAddress (F : CNF V) (o : Occurrence F) : Half F := (.inl o,false)

omit [Fintype V] in
private theorem clauseAddress_inj (F : CNF V) : Function.Injective (clauseAddress F) :=
  fun _ _ h => Sum.inl.inj (congrArg Prod.fst h)

noncomputable def clauseCount (F : CNF V) (p : Half F) : ℕ :=
  ∑ o : Occurrence F, if clauseAddress F o=p then 1 else 0

noncomputable def variableCount (F : CNF V) (p : Half F) : ℕ :=
  ∑ v : V, countByEq (physicalVar F v).flatten p

omit [Fintype V] in
theorem clause_count_at (F : CNF V) (o : Occurrence F) :
    clauseCount F (clauseAddress F o)=1 := by
  unfold clauseCount
  simp [Function.Injective.eq_iff (clauseAddress_inj F)]

/-- Exact one port per half wire across both kinds of old nodes. -/
theorem counts_cover (F : CNF V) (p : Half F) :
    clauseCount F p + variableCount F p=1 := by
  rcases p with ⟨o|i,b⟩
  · cases b
    · change clauseCount F (clauseAddress F o)+_ = _
      rw [clause_count_at]
      simp [variableCount,variable_count_external]
    · simp [clauseCount,clauseAddress,variableCount,variable_count_external,eq_comm]
  · simp [clauseCount,clauseAddress,variableCount,variable_count_internal,eq_comm]

theorem all_positions (F : CNF V) (w : Half F) :
    (∑ p : OldPort F, if read F p=w then (1:ℕ) else 0) =
      clauseCount F w+variableCount F w := by
  rw [Fintype.sum_sigma, Fintype.sum_sum_type]
  congr 1
  · unfold clauseCount
    rw [Fintype.sum_sigma]
    rfl
  · unfold variableCount
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro v _
    symm
    calc
      _ = ∑ g : Fin (physicalVar F v).length, countByEq ((physicalVar F v).get g) w :=
        flatten_positions (physicalVar F v) w
      _ = _ := by
        apply Finset.sum_congr rfl
        intro g _
        exact count_positions ((physicalVar F v).get g) w

/-- Each half wire has exactly one old index (vertex, local port). -/
theorem unique_port (F : CNF V) (w : Half F) :
    ∃! p : OldPort F, read F p=w := by
  classical
  let s := (Finset.univ : Finset (OldPort F)).filter (fun p => read F p=w)
  have he : s.card=1 := by
    unfold s
    rw [Finset.card_filter,all_positions,counts_cover]
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp he
  have h (q : OldPort F) : read F q=w ↔ q=p := by
    have hq := congrArg (fun t : Finset (OldPort F) => q ∈ t) hp
    simpa [s] using hq
  exact ⟨p,(h p).mpr rfl,fun q hq => (h q).mp hq⟩

noncomputable def rowChart (F : CNF V) : OldPort F ≃ Half F :=
  Equiv.ofBijective (read F) <| by
    constructor
    · intro p q h
      obtain ⟨z,_hz,hle⟩ := unique_port F (read F p)
      exact (hle p rfl).trans (hle q h.symm).symm
    · intro w
      obtain ⟨p,hp,_⟩ := unique_port F w
      exact ⟨p,hp⟩

@[simp] theorem rowChart_apply (F : CNF V) (p : OldPort F) :
    rowChart F p=read F p := rfl

#print axioms variable_count_external
#print axioms variable_count_internal
#print axioms counts_cover
#print axioms all_positions
#print axioms unique_port
#print axioms rowChart

end J7R10Counts

