import Mathlib.Data.List.Dedup
import RootIncidence
import S11Literal

/-! Root-Separation (A); quantitative-reduction.tex 65–94, 363–369.
The sparse construction retains ordinary unit clauses as tensors. -/

namespace RootSeparation.Entry

open GraphCutMoments SourceDensity
open S8.Uncloned
open scoped BigOperators
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V))

/-- An orientation encoding a simple undirected graph. -/
structure Simple : Prop where
  loopless : ∀ e ∈ E, e.1 ≠ e.2
  oriented : ∀ u v, (u,v) ∈ E → (v,u) ∉ E

abbrev Clause := V ⊕ E
abbrev OriginalEdge := S8.Uncloned.OriginalEdge E
abbrev Wire := S8.Uncloned.Wire E
abbrev OldVertex := S8.Uncloned.Vertex E

def clause (σ : V → Bool) : Clause E → List (V × Bool)
  | .inl v => [(v,σ v)]
  | .inr e => [(e.1.1,true),(e.1.2,true)]

def portClause : Incidence E → Clause E
  | .inl v => .inl v
  | .inr (e,_) => .inr e

def portIndex : Incidence E → ℕ
  | .inl _ => 0
  | .inr (_,b) => b.toNat

def portLiteral (σ : V → Bool) : Incidence E → V × Bool
  | .inl v => (v,σ v)
  | .inr (e,false) => (e.1.1,true)
  | .inr (e,true) => (e.1.2,true)

theorem literalAt (σ : V → Bool) (p : Incidence E) :
    (clause E σ (portClause E p))[portIndex E p]? = some (portLiteral E σ p) := by
  rcases p with (v | ⟨e,b⟩)
  · rfl
  · cases b <;> rfl

theorem clause_mem (σ : V → Bool) (c : List (V × Bool)) :
    c ∈ PinnedCNF.formula E σ ↔ ∃ i, clause E σ i = c := by
  simp only [PinnedCNF.formula, List.mem_append, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨v,rfl⟩ | ⟨e,he,rfl⟩)
    · exact ⟨.inl v,rfl⟩
    · exact ⟨.inr ⟨e,he⟩,rfl⟩
  · rintro ⟨v | e,rfl⟩
    · exact Or.inl ⟨v,rfl⟩
    · exact Or.inr ⟨e.val,e.property,rfl⟩

theorem clause_nodup_vars (simple : Simple E) (σ : V → Bool) (i : Clause E) :
    ((clause E σ i).map Prod.fst).Nodup := by
  cases i with
  | inl v => simp [clause]
  | inr e => simpa [clause] using simple.loopless _ e.property

theorem clause_distinct (simple : Simple E) (σ : V → Bool) :
    Function.Injective (fun i => (clause E σ i).toFinset) := by
  intro i j h
  rcases i with (v | e) <;> rcases j with (w | f)
  all_goals dsimp only at h
  · exact congrArg Sum.inl (by simpa [clause] using congrArg (Finset.image Prod.fst) h)
  · have a := simple.loopless _ f.property
    have h1 : (f.val.1,true) ∈ (clause E σ (.inl v)).toFinset := by rw [h]; simp [clause]
    have h2 : (f.val.2,true) ∈ (clause E σ (.inl v)).toFinset := by rw [h]; simp [clause]
    simp [clause] at h1 h2
    exact (a (h1.1.trans h2.1.symm)).elim
  · have a := simple.loopless _ e.property
    have h1 : (e.val.1,true) ∈ (clause E σ (.inl w)).toFinset := by rw [← h]; simp [clause]
    have h2 : (e.val.2,true) ∈ (clause E σ (.inl w)).toFinset := by rw [← h]; simp [clause]
    simp [clause] at h1 h2
    exact (a (h1.1.trans h2.1.symm)).elim
  · have h1 : (e.val.1,true) ∈ (clause E σ (.inr f)).toFinset := by rw [← h]; simp [clause]
    have h2 : (e.val.2,true) ∈ (clause E σ (.inr f)).toFinset := by rw [← h]; simp [clause]
    simp [clause] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact (simple.loopless _ e.property (h1.trans h2.symm)).elim
    · exact congrArg Sum.inr (Subtype.ext (Prod.ext h1 h2))
    · exact (simple.oriented _ _ e.property (show (e.val.2,e.val.1) ∈ E from (Prod.ext h2.symm h1.symm : f.val = (e.val.2,e.val.1)) ▸ f.property)).elim
    · exact (simple.loopless _ e.property (h1.trans h2.symm)).elim

theorem formula_nodup (σ : V → Bool) : (PinnedCNF.formula E σ).Nodup := by
  unfold PinnedCNF.formula
  apply List.Nodup.append
  · exact (Finset.nodup_toList _).map (by intro v w h; simpa using congrArg (fun l => (List.head? l).map Prod.fst) h)
  · exact (Finset.nodup_toList _).map (by
      intro e f h
      simp at h
      exact Prod.ext h.1 h.2)
  · intro c hp he
    obtain ⟨v,_,rfl⟩ := List.mem_map.1 hp
    obtain ⟨e,_,h⟩ := List.mem_map.1 he
    simp at h

def Tautological (c : List (V × Bool)) : Prop :=
  ∃ v, (v,false) ∈ c ∧ (v,true) ∈ c

theorem no_trivial_clause (σ : V → Bool) (c : List (V × Bool))
    (hc : c ∈ PinnedCNF.formula E σ) : c ≠ [] ∧ ¬ Tautological c := by
  obtain ⟨i,rfl⟩ := (clause_mem E σ c).mp hc
  rcases i with (v | e)
  · cases h : σ v <;> simp [clause, Tautological, h]
  · simp [clause, Tautological]

/-- Exact effect of including the subsumption rule of main_full_version.tex:3577–3579.
A pin subsumes a positive edge iff that endpoint has a positive pin. -/
def survivingEdges (σ : V → Bool) :=
  E.filter fun e => σ e.1 = false ∧ σ e.2 = false

theorem survives_iff (σ : V → Bool) (e : E) :
    e.val ∈ survivingEdges E σ ↔
      ¬ ∃ v, (clause E σ (.inl v)).toFinset ⊆ (clause E σ (.inr e)).toFinset := by
  classical
  have h (v : V) : (clause E σ (.inl v)).toFinset ⊆ (clause E σ (.inr e)).toFinset ↔
      (v = e.val.1 ∨ v = e.val.2) ∧ σ v = true := by
    rw [show (clause E σ (.inl v)).toFinset = {(v,σ v)} by simp [clause],
      Finset.singleton_subset_iff]
    simp [clause]
    tauto
  simp only [h, survivingEdges, Finset.mem_filter, e.property, true_and]
  constructor
  · rintro ⟨hl,hr⟩ ⟨v,hv,hs⟩
    rcases hv with rfl | rfl <;> simp_all
  · intro h
    constructor
    · cases h₁ : σ e.val.1
      · rfl
      · exact (h ⟨e.val.1, Or.inl rfl, h₁⟩).elim
    · cases h₂ : σ e.val.2
      · rfl
      · exact (h ⟨e.val.2, Or.inr rfl, h₂⟩).elim

theorem allPositive_subsumption : survivingEdges E (fun _ => true) = ∅ := by
  simp [survivingEdges]

theorem allNegative_subsumption : survivingEdges E (fun _ => false) = E := by
  simp [survivingEdges]

abbrev n := Fintype.card V
def m := n (V := V) + E.card
def size := n (V := V) + m E
def initialPrecision := n (V := V) + 1
def order : ℕ := 1

theorem formula_length (σ : V → Bool) : (PinnedCNF.formula E σ).length = m E := by
  simp [PinnedCNF.formula, m]

def useSparse (n m : ℕ) : Prop := m ≤ n * Nat.clog 2 (Nat.clog 2 n)

noncomputable def row (reg : ∀ v, degree E v = 3) : Wire E → OldVertex E :=
  S8.Uncloned.old E reg

def column : Wire E → OriginalEdge E := Prod.fst

theorem col_degree (v : OriginalEdge E) : fiberCount (column E) v = 2 := by
  classical
  rw [fiberCount, ← Fintype.card_subtype]
  let eqv : {w : Wire E // column E w = v} ≃ Bool :=
    { toFun := fun w => w.val.2
      invFun := fun b => ⟨(v,b),rfl⟩
      left_inv := fun w => Subtype.ext (Prod.ext (w.property.symm) rfl)
      right_inv := fun _ => rfl }
  simpa using Fintype.card_congr eqv

theorem slot_bijective (reg : ∀ v, degree E v = 3) :
    Function.Bijective (S8.Uncloned.slot E reg) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨S8.Uncloned.slot_injective E reg, ?_⟩
  have h := regular_edge_count E 3 reg
  simp only [Incidence, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe]
  omega

theorem row_degree (reg : ∀ v, degree E v = 3) (v : OldVertex E) :
    fiberCount (row E reg) v ≤ 3 := S8.Uncloned.old_degree E reg v

theorem wire_count (reg : ∀ v, degree E v = 3) :
    Fintype.card (Wire E) = 10 * n (V := V) := S8.Uncloned.wire_count E reg

theorem network_count (reg : ∀ v, degree E v = 3) (σ : V → Bool) :
    networkCount E reg σ = PinnedCNF.modelCount (PinnedCNF.formula E σ) :=
  countUncloned E reg σ

theorem dimensions (reg : ∀ v, degree E v = 3) :
    2 * m E = 5 * n (V := V) ∧ 2 * size E = 7 * n (V := V) := by
  have h := regular_edge_count E 3 reg
  unfold size m n
  omega

theorem sparse_dispatch (reg : ∀ v, degree E v = 3) (hn : 16 < n (V := V)) :
    useSparse (n (V := V)) (m E) := by
  have h := (dimensions E reg).1
  have hl : 4 < Nat.clog 2 (n (V := V)) :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hn
  have hv : 2 < Nat.clog 2 (Nat.clog 2 (n (V := V))) :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hl
  unfold useSparse
  exact (show m E ≤ n (V := V) * 3 by omega).trans (Nat.mul_le_mul_left _ hv)

theorem root_active (reg : ∀ v, degree E v = 3) (hn : 16 < n (V := V)) :
    S11.leafThreshold (size E) < Fintype.card (Wire E) := by
  have hd := (dimensions E reg).2
  have hs : 1 < size E := by omega
  have hl : 0 < S11.lambda (size E) :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by simpa using hs)
  have h := S11.threshold_le_size _ (Nat.sqrt_pos.2 hl)
  rw [wire_count E reg]
  omega

/-- The optional sign-independent literal and duplicate cleanup also
leaves this pinned formula unchanged. Subsumption has a different effect. -/
noncomputable def simpleNormalize (F : Std.Sat.CNF V) : Std.Sat.CNF V := by
  classical
  exact ((F.map List.dedup).dedup).filter (fun c => !decide (Tautological c))

theorem simpleNormalize_pinned (simple : Simple E) (σ : V → Bool) :
    simpleNormalize (PinnedCNF.formula E σ) = PinnedCNF.formula E σ := by
  classical
  have hmap : (PinnedCNF.formula E σ).map List.dedup = PinnedCNF.formula E σ := by
    conv_rhs => rw [← List.map_id (PinnedCNF.formula E σ)]
    apply List.map_congr_left
    intro c hc
    obtain ⟨i,rfl⟩ := (clause_mem E σ c).mp hc
    exact List.dedup_eq_self.mpr (List.Nodup.of_map Prod.fst (clause_nodup_vars E simple σ i))
  unfold simpleNormalize
  rw [hmap, (formula_nodup E σ).dedup]
  exact List.filter_eq_self.mpr (fun c hc => by simp [(no_trivial_clause E σ c hc).2])

theorem allPositive_after_subsumption (reg : ∀ v, degree E v = 3)
    (hn : 0 < n (V := V)) :
    (PinnedCNF.formula (survivingEdges E (fun _ => true)) (fun _ => true)).length <
      (PinnedCNF.formula E (fun _ => true)).length := by
  rw [allPositive_subsumption, formula_length, formula_length]
  have h := regular_edge_count E 3 reg
  change 0 < Fintype.card V at hn
  have hpos : 0 < E.card := by omega
  simpa [m, n] using (Nat.lt_add_of_pos_right (n := Fintype.card V) hpos)

inductive Dispatch
  | zero | free | enumerate | sparse | dense
  deriving DecidableEq

/-- The dispatcher with sparse inputs given directly to reduction:65–94.
The optional dense normalization is represented by the surviving-edge result above. -/
noncomputable def dispatch (F : Std.Sat.CNF V) : Dispatch := by
  classical
  let C := F.filter (fun c => !decide (Tautological c))
  exact if [] ∈ C then .zero else if C = [] then .free
    else if n (V := V) < 20 then .enumerate
    else if useSparse (n (V := V)) C.length then .sparse else .dense

theorem dispatch_pinned (reg : ∀ v, degree E v = 3)
    (σ : V → Bool) (hn : 20 ≤ n (V := V)) :
    dispatch (PinnedCNF.formula E σ) = .sparse := by
  classical
  have hnone := fun c hc => no_trivial_clause E σ c hc
  have hfilter : (PinnedCNF.formula E σ).filter (fun c => !decide (Tautological c)) =
      PinnedCNF.formula E σ := List.filter_eq_self.mpr (fun c hc => by simp [(hnone c hc).2])
  have he : [] ∉ PinnedCNF.formula E σ := fun h => (hnone [] h).1 rfl
  have hne : PinnedCNF.formula E σ ≠ [] := by
    intro h
    have hl := formula_length E σ
    rw [h, List.length_nil, m] at hl
    omega
  simp [dispatch, hfilter, he, hne, formula_length, Nat.not_lt.mpr hn,
    sparse_dispatch E reg (by omega : 16 < n (V := V))]

theorem pin_occurs (σ : V → Bool) (v : V) :
    [(v,σ v)] ∈ PinnedCNF.formula E σ :=
  (clause_mem E σ _).2 ⟨.inl v,rfl⟩

#check @dispatch_pinned
#check @literalAt
#check @row
#check @column
#check @dimensions
#check @wire_count
#check @root_active
#print axioms simpleNormalize_pinned
#print axioms allPositive_after_subsumption
#print axioms dispatch_pinned
#print axioms literalAt
#print axioms clause_nodup_vars
#print axioms clause_distinct
#print axioms no_trivial_clause
#print axioms survives_iff
#print axioms allPositive_subsumption
#print axioms slot_bijective
#print axioms row_degree
#print axioms col_degree
#print axioms wire_count
#print axioms network_count
#print axioms sparse_dispatch
#print axioms root_active

end RootSeparation.Entry
