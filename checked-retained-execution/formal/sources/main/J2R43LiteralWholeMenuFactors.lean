import J2R43LiteralWholeMenuGeometry
import J9R15FrozenErasureGeneric
import J6R12RepackBoolean

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 16
set_option linter.unusedSectionVars false

/-! No coefficient premise and no tail oracle: preserve the actual old
rows and split the binary subdivision columns using their true ports. -/
namespace J2R43LiteralWholeMenu
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral J6R11Integral
open DenominatorBudget Paper5.D1Literal Paper5.HybridClosure
open J9R14LowPrecisionGeometry J9R14LowPrecisionSlots J9R14LowPrecisionTiedCube
open J9R15FrozenErasureGeneric

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {reg : ∀ v,GraphCutMoments.degree F v=3}
variable {a : ℕ} [Nonempty (MainClonedCNF.Port F)]
local notation "E" => (DWire F)
local notation "C" => (MainClonedCNF.Port F)
local notation "N" => (dNetwork F reg)

abbrev protect (P : PhysicalPacking (dNetwork F reg) a (Fin 64)) (t : ℤ) :
    DWire F→Option ↥(actualKept P t) :=
  protectedOwner (nativeSeats (fun e : E=>P.seat e) (fun e : E=>P.seat e))
    (Finset.univ : Finset C) (vertexOwner P.seat) t

variable (P : PhysicalPacking (dNetwork F reg) a (Fin 64)) (t : ℤ)

theorem true_owner_iff (e : E) (u : ↥(actualKept P t)) :
    (protect P t) e=some u ↔ e.1=u.val := by
  letI : DecidableEq (MainClonedCNF.Port F) := fun x y => Classical.propDecidable (x=y)
  have he : vertexOwner P.seat (P.seat e)=e.1 := actual_owner P e
  unfold protect protectedOwner
  change (if h : vertexOwner P.seat (P.seat e)∈actualKept P t
    then some (⟨vertexOwner P.seat (P.seat e),h⟩ : ↥(actualKept P t)) else none)=some u ↔ e.1=u.val
  by_cases h : vertexOwner P.seat (P.seat e)∈actualKept P t
  · rw [dif_pos h]
    exact ⟨fun hx => he.symm.trans (congrArg Subtype.val (Option.some.inj hx)),
      fun hx => congrArg some (Subtype.ext (he.trans hx))⟩
  · rw [dif_neg h]
    constructor
    · intro hx
      cases hx
    · intro hx
      exact (h ((he.trans hx).symm ▸ u.property)).elim

theorem unprotected_read (X : E→Bool) (e : E) (h : e.1∉actualKept P t) :
    unlift (protect P t) (restrict (protect P t) X) e=X e := by
  letI : DecidableEq (MainClonedCNF.Port F) := fun x y => Classical.propDecidable (x=y)
  have he : vertexOwner P.seat (P.seat e)=e.1 := actual_owner P e
  have hn : vertexOwner P.seat (P.seat e)∉actualKept P t := fun h' => h (he ▸ h')
  have hp : (protect P t) e=none := by
    unfold protect protectedOwner
    change (if h' : vertexOwner P.seat (P.seat e)∈actualKept P t
      then some (⟨vertexOwner P.seat (P.seat e),h'⟩ : ↥(actualKept P t)) else none)=none
    rw [dif_neg hn]
  simp [unlift,hp,restrict]

theorem tied_is_actual_pairs (X : E→Bool) :
    Tied (protect P t) X ↔ ∀ c∈(actualKept P t), X (c,false)=X (c,true) := by
  constructor
  · intro h c hc
    exact h ⟨c,hc⟩ (c,false) (c,true)
      ((true_owner_iff P t _ _).mpr rfl) ((true_owner_iff P t _ _).mpr rfl)
  · intro h u e e' he he'
    have h0 := (true_owner_iff P t e u).mp he
    have h1 := (true_owner_iff P t e' u).mp he'
    obtain ⟨c,b⟩ := e
    obtain ⟨c',b'⟩ := e'
    change c=u.val at h0
    change c'=u.val at h1
    subst c
    subst c'
    have hh := h u.val u.property
    cases b <;> cases b'
    · rfl
    · exact hh
    · exact hh.symm
    · rfl

def originalRest (σ : W→Bool) (Y : E→Bool) (Z : Rest (protect P t)→Bool) : Prop :=
  (∀ r : DOld F, oldRowTruth F reg σ (.inl r) (assignment N Y (.inl r))=true) ∧
  ∀ c : C, c∉(actualKept P t) → unlift (protect P t) Z (c,false)=unlift (protect P t) Z (c,true)

def actualTail (σ : W→Bool) (Y : E→Bool) (Z : Rest (protect P t)→Bool) : TwoLocal :=
  if originalRest P t σ Y Z then 1 else 0

theorem col_flag (σ : W→Bool) (X : E→Bool) (c : C) :
    oldRowTruth F reg σ (.inr c) (assignment N X (.inr c))=true ↔ X (c,false)=X (c,true) := by
  change decide (X (c,false)=X (c,true))=true ↔ _
  simp

theorem actual_flags_split (σ : W→Bool) (Y X : E→Bool) :
    ((∀ r : DOld F, oldRowTruth F reg σ (.inl r) (assignment N Y (.inl r))=true) ∧
      (∀ c : C, oldRowTruth F reg σ (.inr c) (assignment N X (.inr c))=true)) ↔
      Tied (protect P t) X ∧ originalRest P t σ Y (restrict (protect P t) X) := by
  constructor
  · rintro ⟨hY,hX⟩
    refine ⟨(tied_is_actual_pairs P t X).mpr (fun c _ => (col_flag (reg:=reg) σ X c).mp (hX c)),hY,?_⟩
    intro c h
    rw [unprotected_read P t X (c,false) h,unprotected_read P t X (c,true) h]
    exact (col_flag (reg:=reg) σ X c).mp (hX c)
  · rintro ⟨hTie,hY,hRest⟩
    refine ⟨hY,fun c => (col_flag (reg:=reg) σ X c).mpr ?_⟩
    by_cases hc : c∈(actualKept P t)
    · exact (tied_is_actual_pairs P t X).mp hTie c hc
    · simpa only [unprotected_read P t X (c,false) hc,unprotected_read P t X (c,true) hc] using hRest c hc

private theorem prod_flags {R I : Type*} [CommRing R] [Fintype I] (p : I→Prop)
    [∀ i,Decidable (p i)] [Decidable (∀ i,p i)] :
    (∏ i : I, if p i then (1:R) else 0)=if (∀ i, p i) then 1 else 0 := by
  by_cases h : ∀ i, p i
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i _ => if_pos (h i))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private theorem mul_flags {R : Type*} [CommRing R] (p q : Prop)
    [Decidable p] [Decidable q] [Decidable (p∧q)] :
    (if p then (1:R) else 0)*(if q then 1 else 0)=if p∧q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]

theorem original_created_flag (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    (p₀ : ℕ) (hp₀ : 0<p₀) (σ : W→Bool) (v : DOld F⊕C) (X : E→Bool) :
    (oldRowFile F reg f p₀ σ v).frozen hf (assignment N X v)=
      (if oldRowTruth F reg σ v (assignment N X v) then 1 else 0 : IntRing f 1) := by
  exact J6R12Repack.canonical_lift_bool p₀ hp₀ f hf hd 1 (by decide) _

theorem source_frozen_split (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    (p₀ p : ℕ) (hp₀ : 0<p₀) (σ : W→Bool) :
    FrozenSplit P p (oldRowFile F reg f p₀ σ) hf Finset.univ (vertexOwner P.seat) (t:=t)
      (actualTail P t σ) := by
  intro Y X
  change (reduce p f 1 (rowProduct N (oldRowFile F reg f p₀ σ) hf Y) *
    reduce p f 1 (colProduct N (oldRowFile F reg f p₀ σ) hf X) : Box f 1 p) =
    guardWeight (protect P t) X * J6ZeroTransport.reduceAt p (box_two_nil p f 1)
      (actualTail P t σ Y (restrict (protect P t) X))
  rw [rowProduct,colProduct,map_prod,map_prod]
  simp_rw [original_created_flag (reg:=reg) f hf hd p₀ hp₀ σ,apply_ite,map_one,map_zero]
  rw [prod_flags (fun r : DOld F => oldRowTruth F reg σ (.inl r) (assignment N Y (.inl r))=true),
    prod_flags (fun c : C => oldRowTruth F reg σ (.inr c) (assignment N X (.inr c))=true),
    guard_weight,actualTail,apply_ite (J6ZeroTransport.reduceAt p (box_two_nil p f 1)),
    map_one,map_zero,mul_flags,mul_flags]
  have h := actual_flags_split P t σ Y X
  by_cases hh : Tied (protect P t) X ∧ originalRest P t σ Y (restrict (protect P t) X)
  · rw [if_pos (h.mpr hh),if_pos hh]
  · rw [if_neg (fun h' => hh (h.mp h')),if_neg hh]

#print axioms true_owner_iff
#print axioms unprotected_read
#print axioms tied_is_actual_pairs
#print axioms actual_flags_split
#print axioms original_created_flag
#print axioms source_frozen_split

end
end J2R43LiteralWholeMenu