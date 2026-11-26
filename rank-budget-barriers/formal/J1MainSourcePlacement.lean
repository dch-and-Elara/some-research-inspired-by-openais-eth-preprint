import MainProbe
import DiagonalAbundance
import Mathlib.Tactic

/-! MAIN original incidence packing, before contraction. The source copy
rows and the private projection are explicit. Cells and copied occupancy do
not appear as opaque premises in the resulting diagonal layout. -/
namespace J1MainSourcePlacement
open scoped BigOperators Polynomial
open MainProbe
universe i s e v f a
variable {I : Type i} {S : Type s} {E : Type e} {V : Type v} {F : Type f} {A : Type a}

structure IncidenceData (I S E V F : Type*) where
  var : E → V
  factor : E → F
  wordVar : V → I → S
  wordFactor : F → I → S

def IncidenceData.cell (data : IncidenceData I S E V F) (e : E) : Cell I S :=
  (data.wordVar (data.var e),data.wordFactor (data.factor e))

abbrev CellFibre (data : IncidenceData I S E V F) (u : Cell I S) :=
  {e : E // data.cell e = u}

open Classical in
noncomputable instance cellFibreFinite [Fintype E] (data : IncidenceData I S E V F) (u : Cell I S) :
    Fintype (CellFibre data u) := Fintype.ofFinite _

open Classical in
/-- Translating the actual source load count into the size of the fibre to
be placed in distinct copies. -/
theorem fibre_eq_load [Fintype E] (data : IncidenceData I S E V F) (u : Cell I S) :
    Fintype.card (CellFibre data u) =
      (Finset.univ.filter (fun e : E => data.cell e = u)).card := by
  classical
  let eqv : CellFibre data u ≃ ↥(Finset.univ.filter (fun e : E => data.cell e = u)) :=
    Equiv.subtypeEquivRight (fun e => by simp)
  rw [Fintype.card_congr eqv,Fintype.card_coe]

/-- Given h available copies, place each physical incidence in its actual
ordered cell using the enumeration index of its fibre. -/
noncomputable def copyIndex [Fintype E] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h) (e : E) : Fin h :=
  Fin.castLE (cap (data.cell e)) ((Fintype.equivFin _) ⟨e,rfl⟩)

theorem copyIndex_at_label [Fintype E] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h) (e : E)
    (u : Cell I S) (hu : data.cell e = u) :
    copyIndex data h cap e =
      Fin.castLE (cap u) ((Fintype.equivFin (CellFibre data u)) ⟨e,hu⟩) := by
  subst u
  rfl

noncomputable def position [Fintype E] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h) (e : E) : Fin h × Cell I S :=
  (copyIndex data h cap e,data.cell e)

theorem position_injective [Fintype E] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h) :
    Function.Injective (position data h cap) := by
  intro e e' hx
  have hu : data.cell e' = data.cell e := (congrArg Prod.snd hx).symm
  have hc : copyIndex data h cap e = copyIndex data h cap e' := congrArg Prod.fst hx
  rw [copyIndex_at_label data h cap e' (data.cell e) hu] at hc
  have heq : (Fintype.equivFin (CellFibre data (data.cell e))) ⟨e,rfl⟩ =
      (Fintype.equivFin (CellFibre data (data.cell e))) ⟨e',hu⟩ :=
    Fin.ext (congrArg (fun i : Fin h => i.val) hc)
  exact congrArg Subtype.val ((Fintype.equivFin _).injective heq)

/-- The source embedding puts variable x_v in an occupied slot and zero
in nonoccupied slots. Here only the occupied-variable part is recorded. -/
noncomputable def occupied [Fintype E] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h)
    (c : Fin h) (u : Cell I S) : Option V := by
  classical
  exact if hex : ∃ e, position data h cap e = (c,u)
    then some (data.var (Classical.choose hex)) else none

theorem occupied_at [Fintype E] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h) (e : E) :
    occupied data h cap (copyIndex data h cap e) (data.cell e) = some (data.var e) := by
  classical
  let hex : ∃ e', position data h cap e' = (copyIndex data h cap e, data.cell e) := ⟨e,rfl⟩
  unfold occupied
  rw [dif_pos hex]
  exact congrArg (some ∘ data.var) ((position_injective data h cap) (Classical.choose_spec hex))

theorem empty_slot [Fintype E] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h)
    (c : Fin h) (u : Cell I S)
    (missing : ¬∃ e, position data h cap e = (c,u)) : occupied data h cap c u = none := by
  classical
  simp [occupied,missing]

/-- A complete diagonal layout as used by NativeJ2, derived from actual
variable/factor words, fibre placement and the equality of the two words. -/
noncomputable def sourceLayout [Fintype E] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h)
    (pin : A → E) (diag : ∀ a, (data.cell (pin a)).1 = (data.cell (pin a)).2) :
    DiagonalLayout I S V (Fin h) A where
  occupied := occupied data h cap
  variableWord := data.wordVar
  slot a := data.cell (pin a)
  copy a := copyIndex data h cap (pin a)
  pinVar a := data.var (pin a)
  localSlot a := occupied_at data h cap (pin a)
  variableLabel _ := rfl
  diagonal := diag

/-- A row of the actual block-diagonal copied auxiliary matrix. -/
def copiedRow {C : Type*} [DecidableEq C] (c : C) (psi : Cell I S → ℚ)
    (z : C × Cell I S) : ℚ :=
  if z.1 = c then psi z.2 else 0

theorem copied_row_projection {C : Type*} [Fintype C] [DecidableEq C]
    [Fintype I] [DecidableEq I] [Fintype S]
    (c : C) (psi : Cell I S → ℚ) (x : C → Cell I S → ℚ) :
    (∑ z : C × Cell I S, copiedRow c psi z * x z.1 z.2) =
       ∑ u : Cell I S, psi u * x c u := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
  · simp [copiedRow]
  · intro d _ hd
    simp [copiedRow,hd]

section Count
variable [Fintype E]
variable [Fintype A]

abbrev Diagonal (data : IncidenceData I S E V F) (pin : A → E) :=
  {a : A // (data.cell (pin a)).1 = (data.cell (pin a)).2}

noncomputable instance diagFinite (data : IncidenceData I S E V F) (pin : A → E) :
    Fintype (Diagonal data pin) := Fintype.ofFinite _

noncomputable def enumerateLayout (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h) (pin : A → E) :
    DiagonalLayout I S V (Fin h) (Fin (Fintype.card (Diagonal data pin))) :=
  sourceLayout data h cap (fun i => pin ((Fintype.equivFin (Diagonal data pin)).symm i).val)
    (fun i => ((Fintype.equivFin (Diagonal data pin)).symm i).property)

open Classical in
/-- An actual graph-only candidate pin belongs to a group exactly if both
words agree and the original factor word assigns it to this group. -/
noncomputable def hits (data : IncidenceData I S E V F) (pin : A → E) (t : I) (g : S) :
    Finset A :=
  Finset.univ.filter (fun p => (data.cell (pin p)).1 = (data.cell (pin p)).2 ∧
    (data.cell (pin p)).2 t = g)

omit [Fintype E] in
theorem mem_hits (data : IncidenceData I S E V F) (pin : A → E) (t : I) (g : S) (p : A) :
    p ∈ hits data pin t g ↔ (data.cell (pin p)).1 = (data.cell (pin p)).2 ∧
      (data.cell (pin p)).2 t = g := by
  classical
  simp [hits]

/-- Actual per-group counts are preserved by numbering the diagonal
vertices; the desired abundance is no longer an independent group input. -/
theorem owned_card_hits [DecidableEq S] (data : IncidenceData I S E V F)
    (h : ℕ) (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h) (pin : A → E) (t : I) (g : S) :
    (ownedPins (enumerateLayout data h cap pin) t g Finset.univ).card =
      (hits data pin t g).card := by
  classical
  let nrm := Fintype.equivFin (Diagonal data pin)
  let op := ownedPins (enumerateLayout data h cap pin) t g Finset.univ
  have hp (i : Fin (Fintype.card (Diagonal data pin))) :
      i ∈ op ↔ (data.cell (pin (nrm.symm i).val)).2 t = g := by
    simp [op,ownedPins,enumerateLayout,sourceLayout,nrm]
  let e : ↥op ≃ ↥(hits data pin t g) :=
    { toFun i := ⟨(nrm.symm i.val).val,(mem_hits data pin t g _).mpr
        ⟨(nrm.symm i.val).property,(hp i.val).mp i.property⟩⟩
      invFun a := ⟨nrm ⟨a.val,((mem_hits data pin t g _).mp a.property).1⟩,
        (hp _).mpr (by simpa using ((mem_hits data pin t g _).mp a.property).2)⟩
      left_inv := by
        intro i
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  exact (Fintype.card_coe op).symm.trans
    ((Fintype.card_congr e).trans (Fintype.card_coe _))

omit [Fintype E] in
theorem hitCount_is_actual_card (data : IncidenceData I S E V F)
    (pin : A → E) (t : I) (g : S) :
    DiagonalAbundance.hitCount t g (data.cell ∘ pin) =
      ((hits data pin t g).card : ℚ) := by
  classical
  rw [DiagonalAbundance.hitCount_eq_card]
  apply congrArg (fun s : Finset A => (s.card : ℚ))
  ext a
  rw [Finset.mem_filter,mem_hits]
  simp only [Finset.mem_univ, true_and, Function.comp_apply]
  constructor <;> rintro ⟨h,hh⟩
  · exact ⟨h,(congrFun h t).symm.trans hh⟩
  · exact ⟨h,(congrFun h t).trans hh⟩

end Count

#print axioms fibre_eq_load
#print axioms position_injective
#print axioms occupied_at
#print axioms empty_slot
#print axioms copied_row_projection
#print axioms owned_card_hits
#print axioms hitCount_is_actual_card

end J1MainSourcePlacement
