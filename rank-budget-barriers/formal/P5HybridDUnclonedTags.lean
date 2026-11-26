import P5HybridDUnclonedGraph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 17000000

/-! Both tie requests use the *same* unique real clause-side pin wire.
The triangle and exterior-mate maps are graph-only and do not constrain
the signs or replace the internal equality-tree wire by a pin. -/
namespace Paper5.HybridDUncloned
open scoped Classical BigOperators
open J6R10Repack J1MainSourceCollision Paper5.HybridClosure

noncomputable section

section Tagged
variable {W K T : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => network F cubic

def liftPinTag (tag : W→K) : Old F→Option K
  | .inr (.inl w) => some (tag w)
  | _ => none

def pinEmbedding : W ↪ Wire F := ⟨pinWire F,real_pin_injective F⟩

omit [Fintype W] in
theorem tagged_wire_iff (tag : W→K) (e : Wire F) (k : K) :
    (liftPinTag F tag ∘ (N).row) e=some k ↔ ∃ w : W,e=pinWire F w ∧ tag w=k := by
  change liftPinTag F tag ((N).row e)=some k ↔ _
  constructor
  · intro h
    cases hr : (N).row e with
    | inl a => simp [hr,liftPinTag] at h
    | inr b =>
      cases b with
      | inl w => exact ⟨w,(pin_row_exact F cubic w e).mp hr,by simpa [hr,liftPinTag] using h⟩
      | inr f => simp [hr,liftPinTag] at h
  · rintro ⟨w,rfl,hw⟩
    change some (tag w)=some k
    exact congrArg some hw

theorem tied_slots_exact (tag : W→K) :
    (tiedSlots (liftPinTag F tag ∘ (N).row)).card=Fintype.card W := by
  have h : tiedSlots (liftPinTag F tag ∘ (N).row)=Finset.univ.map (pinEmbedding F) := by
    ext e
    simp only [tiedSlots,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    constructor
    · intro he
      cases hk : (liftPinTag F tag ∘ (N).row) e with
      | none =>
        have bad : (none:Option K).isSome=true :=
          (congrArg Option.isSome hk.symm).trans he
        cases bad
      | some k =>
        obtain ⟨w,hw,_⟩ := (tagged_wire_iff F cubic tag e k).mp hk
        exact ⟨w,hw.symm⟩
    · rintro ⟨w,rfl⟩
      have hh := (tagged_wire_iff F cubic tag (pinWire F w) (tag w)).mpr ⟨w,rfl,rfl⟩
      change ((liftPinTag F tag ∘ (N).row) (pinWire F w)).isSome
      rw [hh]
      rfl
  rw [h,Finset.card_map,Finset.card_univ]

variable [Fintype T] [DecidableEq K]

theorem tag_fibre_card_of_equiv (e : W≃K×T) (k : K) :
    (tagFibre (liftPinTag F (Prod.fst ∘ e) ∘ (N).row) k).card=Fintype.card T := by
  let pick : T↪Wire F :=
    ⟨fun t=>pinWire F (e.symm (k,t)),fun s t h=>
      congrArg Prod.snd (e.symm.injective (real_pin_injective F h))⟩
  have h : tagFibre (liftPinTag F (Prod.fst∘e) ∘ (N).row) k=
      Finset.univ.map pick := by
    ext w
    simp only [tagFibre,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    rw [tagged_wire_iff F cubic (Prod.fst ∘ e)]
    constructor
    · rintro ⟨u,rfl,hu⟩
      change (e u).1=k at hu
      refine ⟨(e u).2,?_⟩
      change pinWire F (e.symm (k,(e u).2))=pinWire F u
      rw [show (k,(e u).2)=e u from Prod.ext hu.symm rfl,Equiv.symm_apply_apply]
    · rintro ⟨t,rfl⟩
      refine ⟨e.symm (k,t),rfl,?_⟩
      change (e (e.symm (k,t))).1=k
      rw [Equiv.apply_symm_apply]
  rw [h,Finset.card_map,Finset.card_univ]

end Tagged

section Triangles
variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "reg" => replaced_cubic E baseCubic loopless
local notation "N" => network F reg

def innerTie : Old F→Option V := liftPinTag F Prod.fst
def outerTie : Old F→Option E := liftPinTag F (Prod.fst ∘ (exteriorPort E baseCubic).symm)

theorem actual_inner_pin_tag (w : TriVertex V) :
    innerTie E baseCubic ((N).row (pinWire F w))=some w.1 := rfl

theorem actual_outer_pin_tag (w : TriVertex V) :
    outerTie E baseCubic ((N).row (pinWire F w))=some ((exteriorPort E baseCubic).symm w).1 := rfl

theorem tied_slots_inner :
    (tiedSlots (innerTie E baseCubic ∘ (N).row)).card=Fintype.card (TriVertex V) :=
  tied_slots_exact F reg _

theorem tied_slots_outer :
    (tiedSlots (outerTie E baseCubic ∘ (N).row)).card=Fintype.card (TriVertex V) :=
  tied_slots_exact F reg _

theorem inner_tag_fibre (v : V) : (tagFibre (innerTie E baseCubic ∘ (N).row) v).card=3 := by
  have hf := tag_fibre_card_of_equiv F reg (Equiv.refl (V×Fin 3)) v
  simpa only [Fintype.card_fin] using hf

theorem outer_tag_fibre (e : E) : (tagFibre (outerTie E baseCubic ∘ (N).row) e).card=2 := by
  simpa only [Fintype.card_bool] using
    tag_fibre_card_of_equiv F reg (exteriorPort E baseCubic).symm e
end Triangles

#print axioms tagged_wire_iff
#print axioms tied_slots_exact
#print axioms tag_fibre_card_of_equiv
#print axioms actual_inner_pin_tag
#print axioms actual_outer_pin_tag
#print axioms tied_slots_inner
#print axioms tied_slots_outer
#print axioms inner_tag_fibre
#print axioms outer_tag_fibre
end
end Paper5.HybridDUncloned
