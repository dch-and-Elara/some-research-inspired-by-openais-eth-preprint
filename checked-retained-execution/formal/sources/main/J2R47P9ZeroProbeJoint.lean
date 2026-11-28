import J2R47P9ZeroProbeSeating
import J2R47P9ZeroProbe
import J2R43LiteralWholeMenuGuard

/-! Joint physical construction for the old-row orientation.  The
certified label words and replica count do not change on reseating. -/
namespace J2R47P9ZeroProbe
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking P9BalancedChart J6R10Repack OuterNodePacking
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
open J2R43LiteralWholeMenu
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000
set_option maxRecDepth 2400
set_option linter.unusedSectionVars false
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v, GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)
local notation "C" => MainClonedCNF.Port F
local notation "E" => DWire F

/-- The owner differs from the OR-side physical wire: selecting a column
puts both ports there. The original OR uses its second, tagged port. -/
def originalOrColumn (e : F) (b : Bool) : C := .inr (.inl (e,b))

theorem originalOrColumn_inj {e e' : F} {b b' : Bool}
    (eq : originalOrColumn F e b=originalOrColumn F e' b') :
    (e,b)=(e',b') :=
  Sum.inl.inj (Sum.inr.inj eq)

def originalOrColumns (e : F) : Finset C :=
  (Finset.univ : Finset Bool).image (originalOrColumn F e)

theorem originalOrColumns_disjoint {positive negative : F} (distinct : positive≠negative) :
    Disjoint (originalOrColumns F negative) (originalOrColumns F positive) := by
  refine Finset.disjoint_left.mpr fun u hl hr=>?_
  obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hl
  obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hr
  exact distinct (congrArg Prod.fst (originalOrColumn_inj F (hl.trans hr.symm))).symm

theorem originalOrColumns_at_most_two (e : F) :
    (originalOrColumns F e).card≤2 := by
  calc
    _ ≤ (Finset.univ : Finset Bool).card := Finset.card_image_le
    _ = 2 := by simp

theorem source_p9_guard_and_reserved_or {a : ℕ} [Nonempty C]
    (P : PhysicalPacking N a (Fin 64)) (ha : 0<a) (hb : 4≤P.copies)
    (positive negative : F) (distinct : positive≠negative) :
    ∃ Q : PhysicalPacking N a (Fin 64),
      Q.rowLabel=P.rowLabel ∧ Q.colLabel=P.colLabel ∧ Q.copies=P.copies ∧
      Reserved F reg Q positive negative ∧
      ∀ t : ℤ, t≠0 →
        (Fintype.card C:ℝ)/(2^a:ℕ)≤(actualKept Q t).card+errBudget F a+6 := by
  let label (c : C) (x : Bool) := declaredCell N P.rowLabel P.colLabel (c,x)
  let res (s : Bool) := originalOrColumns F (if s then positive else negative)
  have dis : Disjoint (res false) (res true) := originalOrColumns_disjoint F distinct
  obtain ⟨seat,labels,ends,bound⟩ := guarded_real_layout_with_reservations
    ha hb label (actual_cell_cap P) res dis
    (fun s=>originalOrColumns_at_most_two F (if s then positive else negative))
  let Q := guardReseat P seat labels
  have hs (e : F) (s b : Bool) (eq : e=(if s then positive else negative)) :
      (Q.seat (sourceOrPort F e b)).2=endpointIndex a s := by
    subst e
    exact ends s (originalOrColumn F (if s then positive else negative) b)
      (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩) true
  refine ⟨Q,rfl,rfl,rfl,⟨fun b=>hs positive true b rfl,fun b=>hs negative false b rfl⟩,?_⟩
  intro t ht
  have H := bound Finset.univ t ht
  rw [←real_kept_eq]
  change (Fintype.card C:ℝ)/(2^a:ℕ) ≤
    ((untouched Finset.univ (vertexOwner seat) (matchedColumns Finset.univ
      (realSlot seat) (realSlot seat) t)).card:ℝ)+errBudget F a+6
  simpa only [errBudget,add_assoc] using H

#print axioms originalOrColumn_inj
#print axioms originalOrColumns_disjoint
#print axioms originalOrColumns_at_most_two
#print axioms source_p9_guard_and_reserved_or
end
end J2R47P9ZeroProbe

