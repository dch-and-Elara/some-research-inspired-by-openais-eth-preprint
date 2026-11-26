import P5AlwaysSatOriginalPhysicalCNF
import Mathlib.Data.List.OfFn

/-! The actual literal list at each cloned clause, and exact occurrence
counts at each cloned variable. The sign-independent ports are neither
deduplicated nor replaced by the four-copy construction. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

abbrev ClausePort := Port E T ⊕ (Cycle E T×Bool)

noncomputable def nextCycle : Equiv.Perm (Cycle E T) where
  toFun p := ⟨next E T p.val,(mem_cycle_iff E T _).mpr
    (by change owner (next E T p.val)≠b₀ T
        rw [next_owner]
        exact (mem_cycle_iff E T p.val).mp p.property)⟩
  invFun p := ⟨(next E T).symm p.val,(mem_cycle_iff E T _).mpr
    (by change owner ((next E T).symm p.val)≠b₀ T
        rw [prev_owner]
        exact (mem_cycle_iff E T p.val).mp p.property)⟩
  left_inv p := Subtype.ext ((next E T).symm_apply_apply p.val)
  right_inv p := Subtype.ext ((next E T).apply_symm_apply p.val)

noncomputable def portOwner : ClausePort E T→Port E T
  | .inl p => p
  | .inr (p,false) => p.val
  | .inr (p,true) => next E T p.val

def portFactor : ClausePort E T→CloneFactor E T
  | .inl p => .inl p.1
  | .inr (p,_) => .inr p

def portSign (s : V→Bool) : ClausePort E T→Bool
  | .inl p => (realLiteral s p).2
  | .inr (_,b) => b

def portList : CloneFactor E T→List (ClausePort E T)
  | .inl f => List.ofFn (fun j => .inl ⟨f,j⟩)
  | .inr p => [.inr (p,false),.inr (p,true)]

theorem actual_clause_ports (s : V→Bool) (f : CloneFactor E T) :
    (portList E T f).map (fun p=>(portOwner E T p,portSign E T s p)) =
      clonedClause E T s f := by
  cases f with
  | inl f => simp only [portList,List.map_ofFn,Function.comp_def,portOwner,portSign,
      clonedClause,originalCopies]
  | inr p => rfl

theorem mem_port_list (p : ClausePort E T) (f : CloneFactor E T) :
    p∈portList E T f ↔ portFactor E T p=f := by
  rcases f with f|f
  · rcases p with ⟨g,j⟩|⟨p,b⟩
    · simp only [portList,List.mem_ofFn,portFactor,Sum.inl.injEq]
      constructor
      · rintro ⟨k,hk⟩
        exact (congrArg Sigma.fst hk).symm
      · rintro rfl
        exact ⟨j,rfl⟩
    · simp [portList,List.mem_ofFn,portFactor]
  · rcases p with p|⟨p,b⟩
    · simp [portList,portFactor]
    · cases b <;> simp [portList,portFactor]

theorem literal_mem_iff (s : V→Bool) (f : CloneFactor E T) (w : Port E T) (b : Bool) :
    (w,b)∈clonedClause E T s f ↔ ∃ p : ClausePort E T,
      portFactor E T p=f ∧ portOwner E T p=w ∧ portSign E T s p=b := by
  rw [←actual_clause_ports E T s f,List.mem_map]
  simp only [mem_port_list,Prod.mk.injEq]

theorem port_owner_surjective : Function.Surjective (portOwner E T) :=
  fun p=>⟨.inl p,rfl⟩

theorem port_owner_injective_at_clause [DecidableEq V] [Nonempty V]
    (hC : ∀ v,GraphCutMoments.degree E v=3)
    (p q : ClausePort E T) (hf : portFactor E T p=portFactor E T q)
    (hv : portOwner E T p=portOwner E T q) : p=q := by
  rcases p with p|⟨p,b⟩ <;> rcases q with q|⟨q,c⟩
  · exact congrArg Sum.inl hv
  · cases hf
  · cases hf
  · have hp := Sum.inr.inj hf
    subst q
    cases b <;> cases c
    · rfl
    · exact ((next_ne_self_on_cycle E T hC p) hv.symm).elim
    · exact ((next_ne_self_on_cycle E T hC p) hv).elim
    · rfl

theorem no_tautological_cloned_clause [DecidableEq V] [Nonempty V]
    (hC : ∀ v,GraphCutMoments.degree E v=3) (s : V→Bool)
    (f : CloneFactor E T) (w : Port E T) :
    ¬ ((w,false)∈clonedClause E T s f ∧ (w,true)∈clonedClause E T s f) := by
  rintro ⟨h₀,h₁⟩
  obtain ⟨p,hp,hw₀,hb₀⟩ := (literal_mem_iff E T s f w false).mp h₀
  obtain ⟨q,hq,hw₁,hb₁⟩ := (literal_mem_iff E T s f w true).mp h₁
  have hpq := port_owner_injective_at_clause E T hC p q (hp.trans hq.symm) (hw₀.trans hw₁.symm)
  subst q
  exact Bool.false_ne_true (hb₀.symm.trans hb₁)

theorem cloned_clause_width (s : V→Bool) (f : CloneFactor E T) :
    1≤(clonedClause E T s f).length ∧ (clonedClause E T s f).length≤3 := by
  rcases f with (v|(e|(_|⟨v,b⟩)))|p
  · change 1≤(originalCopies E T s (.inl v)).length ∧ _
    simp [clonedClause,clause]
  · simp [clonedClause,clause]
  · simp [clonedClause,clause]
  · cases b <;> simp [clonedClause,clause]
  · simp [clonedClause,cycleClause]

/-- Reindex the two cycle ports by the *owning* copy, not the clause. -/
noncomputable def incomingReindex : Equiv.Perm (ClausePort E T) :=
  Equiv.sumCongr (Equiv.refl _) (
    { toFun := fun (p,b) => (if b then nextCycle E T p else p,b)
      invFun := fun (p,b) => (if b then (nextCycle E T).symm p else p,b)
      left_inv := by rintro ⟨p,b⟩; cases b <;> simp
      right_inv := by rintro ⟨p,b⟩; cases b <;> simp })

def reindexedOwner : ClausePort E T→Port E T
  | .inl p => p
  | .inr (p,_) => p.val

theorem incoming_reindex_owner (e : ClausePort E T) :
    reindexedOwner E T (incomingReindex E T e)=portOwner E T e := by
  rcases e with e|⟨e,b⟩
  · rfl
  · cases b <;> rfl

noncomputable def ownerFibreEquiv (p : Port E T) :
    {e : ClausePort E T // portOwner E T e=p} ≃
      {e : ClausePort E T // reindexedOwner E T e=p} :=
  (incomingReindex E T).subtypeEquiv (fun e=>by rw [incoming_reindex_owner])

private def reindexedFibreEquiv (p : Port E T) :
    {e : ClausePort E T // reindexedOwner E T e=p} ≃
      Unit ⊕ ({_v : Unit // p∈cycleSlots E T}×Bool) where
  toFun e :=
    match e with
    | ⟨.inl _,_⟩ => .inl ()
    | ⟨.inr (q,b),h⟩ => .inr (⟨(),h ▸ q.property⟩,b)
  invFun e :=
    match e with
    | .inl _ => ⟨.inl p,rfl⟩
    | .inr (q,b) => ⟨.inr (⟨p,q.property⟩,b),rfl⟩
  left_inv := by
    rintro ⟨e,he⟩
    rcases e with e|⟨q,b⟩
    · exact Subtype.ext (congrArg Sum.inl he.symm)
    · apply Subtype.ext
      change Sum.inr ((⟨p,he ▸ q.property⟩ : Cycle E T),b)=Sum.inr (q,b)
      exact congrArg Sum.inr (Prod.ext (Subtype.ext he.symm) rfl)
  right_inv := by
    rintro (_|⟨⟨⟨⟩,_⟩,b⟩)
    · rfl
    · rfl

theorem physical_copy_degree (p : Port E T) :
    Nat.card {e : ClausePort E T // portOwner E T e=p} =
      if p=bonusZeroPort E T then 1 else 3 := by
  classical
  rw [Nat.card_congr (ownerFibreEquiv E T p),Nat.card_congr (reindexedFibreEquiv E T p),
    Nat.card_sum,Nat.card_prod]
  have hu : Nat.card Unit=1 := by simp [Nat.card_eq_fintype_card]
  have hb : Nat.card Bool=2 := by simp [Nat.card_eq_fintype_card]
  rw [hu,hb]
  by_cases hp : p=bonusZeroPort E T
  · have hno : p∉cycleSlots E T := fun h=>(cycle_excludes_exactly_bonus0 E T p).mp h hp
    have he : Nat.card {_v : Unit // p∈cycleSlots E T}=0 :=
      Nat.card_eq_zero.mpr (Or.inl ⟨fun v=>hno v.property⟩)
    rw [he,if_pos hp]
  · have hyes := (cycle_excludes_exactly_bonus0 E T p).mpr hp
    let e : {_v : Unit // p∈cycleSlots E T} ≃ Unit :=
      ⟨fun _=>(),fun _=>⟨(),hyes⟩,fun w=>Subtype.ext (Subsingleton.elim _ _),fun _=>rfl⟩
    rw [Nat.card_congr e,hu,if_neg hp]

theorem physical_copy_degree_le (p : Port E T) :
    Nat.card {e : ClausePort E T // portOwner E T e=p}≤3 := by
  rw [physical_copy_degree]
  split <;> decide

def marked (E : Finset (V×V)) (T : Finset V) : V↪ClausePort E T :=
  ⟨fun v=>.inl (pinPort E T v),fun _ _ h=>Sum.inl.inj (congrArg Sigma.fst (Sum.inl.inj h))⟩

@[simp] theorem marked_factor (v : V) :
    portFactor E T (marked E T v)=.inl (.inl v) := rfl

theorem port_card : Fintype.card (ClausePort E T) =
    Fintype.card (Port E T)+2*(cycleSlots E T).card := by
  simp [ClausePort,Nat.mul_comm]

theorem cloned_formula_length (s : V→Bool) :
    (cloneCNF E T s).length=(formula E T s).length+(cycleSlots E T).card := by
  rw [cloneCNF,List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_sum,
    Fintype.card_coe]
  rw [formula,List.length_map,Finset.length_toList,Finset.card_univ]

theorem original_physical_sizes [DecidableEq V] (s : V→Bool)
    (hC : ∀ v,GraphCutMoments.degree E v=3) :
    (cloneCNF E T s).length=8*Fintype.card V+6*T.card+2 ∧
    2*Fintype.card (ClausePort E T)=33*Fintype.card V+24*T.card+8 ∧
    Fintype.card (ClausePort E T)+Fintype.card (Port E T)=22*Fintype.card V+16*T.card+6 := by
  rw [cloned_formula_length,port_card]
  exact original_nominal_clone_sizes E T s hC

#print axioms actual_clause_ports
#print axioms mem_port_list
#print axioms literal_mem_iff
#print axioms port_owner_surjective
#print axioms port_owner_injective_at_clause
#print axioms no_tautological_cloned_clause
#print axioms cloned_clause_width
#print axioms incoming_reindex_owner
#print axioms physical_copy_degree
#print axioms physical_copy_degree_le
#print axioms marked_factor
#print axioms port_card
#print axioms cloned_formula_length
#print axioms original_physical_sizes
end Paper5.AlwaysSatOriginal.Physical