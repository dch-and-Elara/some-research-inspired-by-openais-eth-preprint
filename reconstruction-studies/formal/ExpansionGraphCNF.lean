import ExpansionGraphBase

namespace Reconstruction.ExpansionGraph

open Finset
open scoped BigOperators

noncomputable section

abbrev CNF (V : Type*) := List (List (V × Bool))

def Satisfies {V : Type*} (F : CNF V) (x : V → Bool) : Prop :=
  ∀ C ∈ F, ∃ l ∈ C, x l.1 = l.2

abbrev Models {V : Type*} (F : CNF V) := {x : V → Bool // Satisfies F x}

def WidthAtMost {V : Type*} (F : CNF V) (w : ℕ) : Prop :=
  ∀ C ∈ F, C.length ≤ w

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev GateVar (G : SimpleGraph V) := V ⊕ G.edgeSet

/-- A canonical representative of an unordered edge, used only to write its clauses. -/
def endpoints (e : G.edgeSet) : V × V := e.val.out

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem endpoints_eq (e : G.edgeSet) : s((endpoints G e).1, (endpoints G e).2) = e.val :=
  Quot.out_eq _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem endpoints_adj (e : G.edgeSet) : G.Adj (endpoints G e).1 (endpoints G e).2 := by
  change s((endpoints G e).1, (endpoints G e).2) ∈ G.edgeSet
  rw [endpoints_eq]
  exact e.property

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem endpoints_ne (e : G.edgeSet) : (endpoints G e).1 ≠ (endpoints G e).2 :=
  (endpoints_adj G e).ne

def gateClauses (e : G.edgeSet) : CNF (GateVar G) :=
  let (u,v) := endpoints G e
  [[(.inr e, false), (.inl u, true)],
   [(.inr e, false), (.inl v, true)],
   [(.inr e, true), (.inl u, false), (.inl v, false)]]

def positiveGraphCNF : CNF V :=
  (univ : Finset G.edgeSet).toList.map fun e =>
    [((endpoints G e).1, true), ((endpoints G e).2, true)]

private def liftCNF {X Y : Type*} (f : X → Y) (F : CNF X) : CNF Y :=
  F.map fun C => C.map fun l => (f l.1, l.2)

def gatePart : CNF (GateVar G) :=
  (univ : Finset G.edgeSet).toList.flatMap (gateClauses G)

def gateExtension (F : CNF V) : CNF (GateVar G) :=
  liftCNF Sum.inl F ++ gatePart G

private theorem satisfies_lift {X Y : Type*} (i : X → Y) (F : CNF X) (x : Y → Bool) :
    Satisfies (liftCNF i F) x ↔ Satisfies F (x ∘ i) := by
  constructor
  · intro h C hC
    obtain ⟨l, hl, hx⟩ := h _ (List.mem_map.mpr ⟨C,hC,rfl⟩)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
    exact ⟨a, ha, hx⟩
  · intro h C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    obtain ⟨a, ha, hx⟩ := h D hD
    exact ⟨(i a.1,a.2), List.mem_map.mpr ⟨a,ha,rfl⟩, hx⟩

private theorem satisfies_append {X : Type*} (F H : CNF X) (x : X → Bool) :
    Satisfies (F ++ H) x ↔ Satisfies F x ∧ Satisfies H x := by
  constructor
  · intro h
    exact ⟨fun C hC => h C (List.mem_append.mpr (Or.inl hC)),
      fun C hC => h C (List.mem_append.mpr (Or.inr hC))⟩
  · intro h C hC
    exact (List.mem_append.mp hC).elim (h.1 C) (h.2 C)

private theorem satisfies_cons {X : Type*} (C : List (X × Bool)) (F : CNF X) (x : X → Bool) :
    Satisfies (C :: F) x ↔ (∃ l ∈ C, x l.1 = l.2) ∧ Satisfies F x := by
  constructor
  · intro h
    exact ⟨h _ (List.mem_cons_self ..), fun D hD => h D (List.mem_cons_of_mem _ hD)⟩
  · intro h D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact h.1
    · exact h.2 D hD

private theorem clause_cons {X : Type*} (a : X × Bool) (C : List (X × Bool)) (x : X → Bool) :
    (∃ l ∈ a :: C, x l.1 = l.2) ↔ x a.1 = a.2 ∨ ∃ l ∈ C, x l.1 = l.2 := by
  constructor
  · rintro ⟨l, hl, he⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Or.inl he
    · exact Or.inr ⟨l,hl,he⟩
  · rintro (he | ⟨l,hl,he⟩)
    · exact ⟨a,List.mem_cons_self ..,he⟩
    · exact ⟨l,List.mem_cons_of_mem _ hl,he⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem satisfies_gateClauses (e : G.edgeSet) (x : GateVar G → Bool) :
    Satisfies (gateClauses G e) x ↔
      x (.inr e) = (x (.inl (endpoints G e).1) && x (.inl (endpoints G e).2)) := by
  rcases he : endpoints G e with ⟨u,v⟩
  simp only [gateClauses, he, satisfies_cons, clause_cons, List.not_mem_nil, false_and,
    exists_false, or_false]
  have hnil : Satisfies ([] : CNF (GateVar G)) x := by simp [Satisfies]
  cases x (.inl u) <;> cases x (.inl v) <;> cases x (.inr e) <;> simp [hnil]

omit [DecidableEq V] in
private theorem satisfies_gatePart (x : GateVar G → Bool) :
    Satisfies (gatePart G) x ↔ ∀ e, Satisfies (gateClauses G e) x := by
  unfold Satisfies gatePart
  simp only [List.mem_flatMap, mem_toList, mem_univ, true_and, forall_exists_index]
  exact ⟨fun h e C hC => h C e hC, fun h C e hC => h e C hC⟩

def gateAssignment (x : V → Bool) : GateVar G → Bool :=
  Sum.elim x fun e => x (endpoints G e).1 && x (endpoints G e).2

omit [DecidableEq V] in
theorem satisfies_gateExtension (F : CNF V) (x : GateVar G → Bool) :
    Satisfies (gateExtension G F) x ↔ Satisfies F (x ∘ Sum.inl) ∧
      x = gateAssignment G (x ∘ Sum.inl) := by
  rw [gateExtension, satisfies_append, satisfies_lift, satisfies_gatePart]
  simp_rw [satisfies_gateClauses]
  constructor
  · rintro ⟨h, hy⟩
    refine ⟨h, ?_⟩
    funext v
    cases v with
    | inl v => rfl
    | inr e => exact hy e
  · rintro ⟨h, hy⟩
    exact ⟨h, fun e => congrFun hy (.inr e)⟩

/-- The extension is parsimonious, with explicit restriction and unique extension maps. -/
def gateModelsEquiv (F : CNF V) : Models F ≃ Models (gateExtension G F) where
  toFun x := ⟨gateAssignment G x.val, (satisfies_gateExtension G F _).mpr ⟨x.property, rfl⟩⟩
  invFun y := ⟨y.val ∘ Sum.inl, ((satisfies_gateExtension G F _).mp y.property).1⟩
  left_inv _ := rfl
  right_inv y := Subtype.ext (((satisfies_gateExtension G F _).mp y.property).2.symm)

omit [DecidableEq V] in
theorem gateExtension_card_models (F : CNF V) :
    Nat.card (Models (gateExtension G F)) = Nat.card (Models F) :=
  Nat.card_congr (gateModelsEquiv G F).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem gateClauses_length (e : G.edgeSet) : (gateClauses G e).length = 3 := by
  rcases h : endpoints G e with ⟨u,v⟩
  simp [gateClauses, h]

omit [DecidableEq V] in
theorem gatePart_length : (gatePart G).length = 3 * Fintype.card G.edgeSet := by
  classical
  unfold gatePart
  rw [List.length_flatMap]
  simp [gateClauses_length, mul_comm]

omit [DecidableEq V] in
theorem gateExtension_length (F : CNF V) :
    (gateExtension G F).length = F.length + 3 * Fintype.card G.edgeSet := by
  rw [gateExtension, List.length_append, gatePart_length]
  simp [liftCNF]

omit [DecidableEq V] in
theorem gateExtension_width {F : CNF V} {w : ℕ} (hw : WidthAtMost F w) :
    WidthAtMost (gateExtension G F) (max 3 w) := by
  intro C hC
  rcases List.mem_append.mp hC with h | h
  · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h
    simpa only [List.length_map] using (hw D hD).trans (le_max_right ..)
  · obtain ⟨e, _, he⟩ := List.mem_flatMap.mp h
    rcases hv : endpoints G e with ⟨u,v⟩
    simp [gateClauses, hv] at he
    rcases he with rfl | rfl | rfl <;> simp

omit [DecidableEq V] in
theorem gateExtension_size (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * Fintype.card (GateVar G) ≤ 5 * Fintype.card V ∧
      2 * (gatePart G).length ≤ 9 * Fintype.card V := by
  have hd : ∑ v, G.degree v ≤ ∑ _v : V, 3 := sum_le_sum fun v _ => hdeg v
  rw [G.sum_degrees_eq_twice_card_edges, SimpleGraph.edgeFinset_card] at hd
  simp only [sum_const, card_univ, smul_eq_mul] at hd
  rw [Fintype.card_sum, gatePart_length]
  omega

def occurs {X : Type*} [DecidableEq X] (v : X) (F : CNF X) : ℕ :=
  (F.map fun C => (C.filter fun l => decide (l.1 = v)).length).sum

omit [Fintype V] [DecidableRel G.Adj] in
private theorem gateClause_occurs_old (e : G.edgeSet) (v : V) :
    occurs (Sum.inl v) (gateClauses G e) = if v ∈ e.val then 2 else 0 := by
  have he := endpoints_eq G e
  have hn := endpoints_ne G e
  rw [← he]
  rcases hv : endpoints G e with ⟨u,w⟩
  simp only [hv] at hn
  simp only [Sym2.mem_iff]
  by_cases h1 : v = u
  · subst v
    have hn' := Ne.symm hn
    simp [occurs, gateClauses, hv, hn, hn']
  · by_cases h2 : v = w
    · subst v
      have hn' := Ne.symm hn
      simp [occurs, gateClauses, hv, hn, hn']
    · simp [occurs, gateClauses, hv, h1, h2, Ne.symm h1, Ne.symm h2]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem gateClause_occurs_new (e f : G.edgeSet) :
    occurs (Sum.inr f) (gateClauses G e) = if e = f then 3 else 0 := by
  rcases hv : endpoints G e with ⟨u,w⟩
  by_cases h : e = f <;> simp [occurs, gateClauses, hv, h]

private theorem occurs_append {X : Type*} [DecidableEq X] (v : X) (F H : CNF X) :
    occurs v (F ++ H) = occurs v F + occurs v H := by
  simp [occurs, List.sum_append]

private theorem occurs_flatMap {X Y : Type*} [DecidableEq X] (v : X) (f : Y → CNF X) (L : List Y) :
    occurs v (L.flatMap f) = (L.map fun y => occurs v (f y)).sum := by
  induction L with
  | nil => rfl
  | cons y L ih => simp [List.flatMap_cons, occurs_append, ih]

private theorem occurs_lift_inl {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (F : CNF X) (v : X) :
    occurs (Sum.inl v : X ⊕ Y) (liftCNF Sum.inl F) = occurs v F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    have hC : ((C.map fun l : X × Bool => ((Sum.inl l.1 : X ⊕ Y), l.2)).filter
        fun l => decide (l.1 = Sum.inl v)).length = (C.filter fun l => decide (l.1 = v)).length := by
      induction C with
      | nil => rfl
      | cons l C ih => rcases l with ⟨u,b⟩; by_cases h : u = v <;> simp [h, ih]
    simpa [liftCNF, occurs] using congrArg₂ (· + ·) hC ih

private theorem occurs_lift_inr {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (F : CNF X) (e : Y) :
    occurs (Sum.inr e) (liftCNF Sum.inl F) = 0 := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [liftCNF, occurs, List.filter_map] using ih

theorem gateExtension_occurs_old (F : CNF V) (v : V) :
    occurs (Sum.inl v) (gateExtension G F) = occurs v F + 2 * G.degree v := by
  classical
  rw [gateExtension, occurs_append, occurs_lift_inl, gatePart, occurs_flatMap]
  rw [Finset.sum_map_toList]
  simp_rw [gateClause_occurs_old]
  rw [← Finset.sum_filter]
  change _ + (∑ _ ∈ incidentFactors G v, 2) = _
  rw [sum_const, incidentFactors_card, smul_eq_mul, mul_comm (G.degree v)]

theorem gateExtension_occurs_new (F : CNF V) (e : G.edgeSet) :
    occurs (Sum.inr e) (gateExtension G F) = 3 := by
  classical
  rw [gateExtension, occurs_append, occurs_lift_inr, zero_add, gatePart, occurs_flatMap]
  rw [Finset.sum_map_toList]
  simp_rw [gateClause_occurs_new]
  simp

def paddingCount (n : ℕ) : ℕ := (128 - n % 128) % 128

theorem paddingCount_le (n : ℕ) : paddingCount n ≤ 127 := by
  unfold paddingCount
  omega

theorem paddingCount_dvd (n : ℕ) : 128 ∣ n + paddingCount n := by
  unfold paddingCount
  omega

abbrev PaddedVar (n : ℕ) := Fin n ⊕ Fin (paddingCount n)

def paddingUnits (n : ℕ) : CNF (PaddedVar n) :=
  (univ : Finset (Fin (paddingCount n))).toList.map fun i => [(Sum.inr i, false)]

def padCNF {n : ℕ} (F : CNF (Fin n)) : CNF (PaddedVar n) :=
  liftCNF Sum.inl F ++ paddingUnits n

theorem satisfies_padCNF {n : ℕ} (F : CNF (Fin n)) (x : PaddedVar n → Bool) :
    Satisfies (padCNF F) x ↔ Satisfies F (x ∘ Sum.inl) ∧ ∀ i, x (Sum.inr i) = false := by
  rw [padCNF, satisfies_append, satisfies_lift]
  simp [Satisfies, paddingUnits]

/-- Every original satisfying assignment has exactly one padded assignment. -/
def paddingModelsEquiv {n : ℕ} (F : CNF (Fin n)) : Models F ≃ Models (padCNF F) where
  toFun x := ⟨Sum.elim x.val (fun _ => false), (satisfies_padCNF F _).mpr
    ⟨x.property, fun _ => rfl⟩⟩
  invFun x := ⟨x.val ∘ Sum.inl, ((satisfies_padCNF F _).mp x.property).1⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    funext v
    cases v with
    | inl v => rfl
    | inr i => exact (((satisfies_padCNF F _).mp x.property).2 i).symm

theorem padCNF_length {n : ℕ} (F : CNF (Fin n)) :
    (padCNF F).length = F.length + paddingCount n := by
  simp [padCNF, paddingUnits, liftCNF]

theorem padCNF_width {n w : ℕ} {F : CNF (Fin n)} (hw : WidthAtMost F w) :
    WidthAtMost (padCNF F) (max 1 w) := by
  intro C hC
  rcases List.mem_append.mp hC with h | h
  · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h
    simpa only [List.length_map] using (hw D hD).trans (le_max_right ..)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    simp

theorem padCNF_occurs_old {n : ℕ} (F : CNF (Fin n)) (v : Fin n) :
    occurs (Sum.inl v) (padCNF F) = occurs v F := by
  rw [padCNF, occurs_append, occurs_lift_inl]
  simp [occurs, paddingUnits]

theorem padCNF_occurs_new {n : ℕ} (F : CNF (Fin n)) (v : Fin (paddingCount n)) :
    occurs (Sum.inr v) (padCNF F) = 1 := by
  rw [padCNF, occurs_append, occurs_lift_inr, zero_add]
  unfold occurs paddingUnits
  rw [List.map_map, Finset.sum_map_toList]
  simp [List.filter_cons, apply_ite List.length]

/-- List implementation when the edge identifiers and their endpoints are supplied.
Each edge emits one block of three clauses. -/
def gatesOfEdgeList {X E : Type*} (EList : List (E × X × X)) : CNF (X ⊕ E) :=
  EList.flatMap fun (e,u,v) =>
    [[(.inr e,false),(.inl u,true)], [(.inr e,false),(.inl v,true)],
      [(.inr e,true),(.inl u,false),(.inl v,false)]]

theorem gatesOfEdgeList_counts {X E : Type*} (EList : List (E × X × X)) :
    (gatesOfEdgeList EList).length = 3*EList.length ∧
    ((gatesOfEdgeList EList).map List.length).sum = 7*EList.length := by
  induction EList with
  | nil => simp [gatesOfEdgeList]
  | cons edge L ih =>
    obtain ⟨e,u,v⟩ := edge
    simp only [gatesOfEdgeList, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil] at ih ⊢
    omega

omit [DecidableEq V] in
theorem gatesOfEdgeList_eq_gatePart :
    gatesOfEdgeList ((univ : Finset G.edgeSet).toList.map (fun e =>
      (e,(endpoints G e).1,(endpoints G e).2))) = gatePart G := by
  simp only [gatesOfEdgeList, gatePart, List.flatMap_map]
  congr 1

/-- The ternary factor indexed by an edge contains both original endpoints. -/
def ternaryGateFactor (e : G.edgeSet) : List (GateVar G × Bool) :=
  [(.inr e, true), (.inl (endpoints G e).1, false), (.inl (endpoints G e).2, false)]

omit [DecidableEq V] in
theorem ternaryGateFactor_mem (e : G.edgeSet) (F : CNF V) :
    ternaryGateFactor G e ∈ gateExtension G F := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨e, by simp, ?_⟩
  rcases h : endpoints G e with ⟨u,v⟩
  simp [gateClauses, ternaryGateFactor, h]

theorem incident_ternaryGateFactor {v : V} {e : G.edgeSet} (h : e ∈ incidentFactors G v) :
    (Sum.inl v, false) ∈ ternaryGateFactor G e := by
  have hv := (mem_incidentFactors G).mp h
  rw [← endpoints_eq G e, Sym2.mem_iff] at hv
  rcases hv with hv | hv <;> simp [ternaryGateFactor, hv]

/-- Parsimonious padding followed by the edge-gate extension on the padded variables. -/
def parsimonious_extension {n : ℕ} (F : CNF (Fin n))
    (G : SimpleGraph (PaddedVar n)) [DecidableRel G.Adj] :
    Models F ≃ Models (gateExtension G (padCNF F)) :=
  (paddingModelsEquiv F).trans (gateModelsEquiv G (padCNF F))

end

end Reconstruction.ExpansionGraph
