import PTPreprocess

namespace RootSeparation.Preprocessing

open GraphCutMoments Finset
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

def owner (E : Finset (V × V)) : S8.Uncloned.Incidence E → V
  | .inl v => v
  | .inr (e,false) => e.val.1
  | .inr (e,true) => e.val.2

private def filteredEdges (E : Finset (V × V)) (p : V × V → Prop) [DecidablePred p] :
    {e : E // p e.val} ≃ ↥(E.filter p) where
  toFun e := ⟨e.val.val,mem_filter.mpr ⟨e.val.property,e.property⟩⟩
  invFun e := ⟨⟨e.val,(mem_filter.mp e.property).1⟩,(mem_filter.mp e.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def ownerParts (E : Finset (V × V)) (v : V) :
    {p : S8.Uncloned.Incidence E // owner E p = v} ≃
      Unit ⊕ ({e : E // e.val.1 = v} ⊕ {e : E // e.val.2 = v}) where
  toFun
    | ⟨.inl _,_⟩ => .inl ()
    | ⟨.inr (e,false),h⟩ => .inr (.inl ⟨e,h⟩)
    | ⟨.inr (e,true),h⟩ => .inr (.inr ⟨e,h⟩)
  invFun
    | .inl _ => ⟨.inl v,rfl⟩
    | .inr (.inl ⟨e,h⟩) => ⟨.inr (e,false),h⟩
    | .inr (.inr ⟨e,h⟩) => ⟨.inr (e,true),h⟩
  left_inv := by
    rintro ⟨w,hw⟩
    rcases w with (x | ⟨e,b⟩)
    · have hx : x = v := hw
      subst x
      rfl
    · cases b <;> rfl
  right_inv := by rintro (⟨⟩ | ⟨e,h⟩ | ⟨e,h⟩) <;> rfl

theorem port_count (E : Finset (V × V)) (v : V) :
    Fintype.card {p : S8.Uncloned.Incidence E // owner E p = v} = degree E v+1 := by
  rw [Fintype.card_congr (ownerParts E v),Fintype.card_sum,Fintype.card_sum,
    Fintype.card_congr (filteredEdges E (fun e => e.1 = v)),
    Fintype.card_congr (filteredEdges E (fun e => e.2 = v))]
  simp only [Fintype.card_unit,Fintype.card_coe,degree]
  omega

def treeVertices (g : ℕ) : ℕ := if g = 3 then 2 else 1

/-- Local shape of the source equality replacement for g+1 ports.
For g=3, each endpoint receives two ports and one internal half-edge. -/
def treeAttach (g : ℕ) (port : Fin (g+1)) : Fin (treeVertices g) :=
  ⟨if g = 3 then port.val/2 else 0, by
    split <;> rename_i h <;> simp [treeVertices,h]
    have := port.isLt
    omega⟩

def localDegree (g : ℕ) (v : Fin (treeVertices g)) : ℕ :=
  (univ.filter fun p : Fin (g+1) => treeAttach g p = v).card + if g = 3 then 1 else 0

theorem local_degree (g : ℕ) (hg : g ≤ 3) (v : Fin (treeVertices g)) :
    localDegree g v = if g = 3 then 3 else g+1 := by
  interval_cases g <;> fin_cases v <;> decide

abbrev BuiltOld (E : Finset (V × V)) :=
  ((v : V) × Fin (treeVertices (degree E v))) ⊕ Entry.Clause E

noncomputable def variablePort (E : Finset (V × V)) (p : S8.Uncloned.Incidence E) :
    Fin (degree E (owner E p)+1) :=
  Fintype.equivFinOfCardEq (port_count E (owner E p)) ⟨p,rfl⟩

/-- Each wire has one original endpoint and one new binary equality midpoint.
An incidence goes from its equality-tree vertex to its real clause.
An internal link is present precisely for the four-port tree. -/
noncomputable def builtOld (E : Finset (V × V)) : BuiltWire E → BuiltOld E
  | (.inl p,false) => .inl ⟨owner E p,treeAttach _ (variablePort E p)⟩
  | (.inl (.inl v),true) => .inr (.inl v)
  | (.inl (.inr (e,_)),true) => .inr (.inr e)
  | (.inr v,b) => .inl ⟨v.val,⟨b.toNat,by rw [treeVertices,if_pos v.property]; cases b <;> decide⟩⟩

def builtMid (E : Finset (V × V)) : BuiltWire E → BuiltLink E := Prod.fst

theorem pin_endpoint (E : Finset (V × V)) (v : V) :
    builtOld E (builtPin E v) = .inr (.inl v) := rfl

theorem mid_degree (E : Finset (V × V)) (q : BuiltLink E) :
    SourceDensity.fiberCount (builtMid E) q = 2 := by
  unfold SourceDensity.fiberCount
  have hh : (univ.filter fun w : BuiltWire E => builtMid E w = q) =
      (univ : Finset Bool).map ⟨fun b => (q,b), by intro a b h; exact congrArg Prod.snd h⟩ := by
    ext w
    rcases w with ⟨p,b⟩
    simp [builtMid,eq_comm]
  rw [hh,card_map]
  decide

theorem normalized_ports (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (σ : V → Bool) (v : V) :
    let E' := Entry.survivingEdges E σ
    Fintype.card {p : S8.Uncloned.Incidence E' // owner E' p = v} = degree E' v + 1 ∧
    ∀ q : Fin (treeVertices (degree E' v)), localDegree (degree E' v) q ≤ 3 := by
  intro E'
  have hg := (surviving_degree E σ v).trans_eq (reg v)
  refine ⟨port_count E' v,?_⟩
  intro q
  rw [local_degree _ hg]
  split <;> omega

theorem propagated_residual (E : Finset (V × V)) (σ : V → Bool) :
    (∀ c ∈ afterPropagatingPins E σ, c = []) ∧
    (afterPropagatingPins E σ = [] ↔ PinnedCNF.AllEdges E σ) := by
  have h : ∀ c ∈ afterPropagatingPins E σ, c = [] := by
    intro c hc
    obtain ⟨a,_,ha⟩ := List.mem_filterMap.mp hc
    split at ha <;> simp_all
  refine ⟨h,?_⟩
  rw [← not_not (a := PinnedCNF.AllEdges E σ), ← propagated_has_empty]
  constructor
  · simp +contextual
  · intro hm
    cases he : afterPropagatingPins E σ with
    | nil => rfl
    | cons c cs =>
      have hc : c ∈ afterPropagatingPins E σ := by simp [he]
      exact (hm (h c hc ▸ hc)).elim

#print axioms port_count
#print axioms local_degree
#print axioms pin_endpoint
#print axioms mid_degree
#print axioms normalized_ports
#print axioms propagated_residual

end RootSeparation.Preprocessing
