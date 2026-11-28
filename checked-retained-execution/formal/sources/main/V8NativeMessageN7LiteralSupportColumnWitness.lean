import V8NativeMessageN7LiteralSupportOrientation

/-! A simultaneous satisfying word for all old column tables, for
every sign word. This fixes all clone-variable incidences to false and
all non-pin clause incidences to true, but does not identify them with
the row-side subdivision bits. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial
open Polynomial J6R10Repack Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)

def columnWitness (σ : W→Bool) : DWire F→Bool
  | (_,false) => false
  | (.inl w,true) => σ w
  | (.inr _,true) => true

omit [Fintype W] in
private theorem clone_column_witness_false (σ : W→Bool) (k : Clone W)
    (p : ParentPorts N (.inl (.inl k))) :
    columnWitness F σ (edge p.val)=false := by
  rcases p with ⟨p,property⟩
  rcases p with ⟨u,b⟩|u
  · cases b
    · change columnWitness F σ (u,false)=false
      cases u <;> rfl
    · simp [owner,dNetwork] at property
  · cases property

theorem witness_satisfies_all_true_old_tables (σ : W→Bool) (u : DOld F) :
    oldRowTruth F reg σ (.inl u) (fun p=>columnWitness F σ (edge p.val))=true := by
  rcases u with k|(v|e|⟨v,j⟩)
  · simp only [oldRowTruth,decide_eq_true_eq]
    intro p q
    exact (clone_column_witness_false F reg σ k p).trans
      (clone_column_witness_false F reg σ k q).symm
  · simp [oldRowTruth,columnWitness,edge]
  · rfl
  · rfl

noncomputable def originalColumnKeep (σ : W→Bool) (y : DWire F→Bool) : Bool :=
  decide (∀ u : DOld F, oldRowTruth F reg σ (.inl u) (fun p=>y (edge p.val))=true)

theorem original_columns_have_joint_word (σ : W→Bool) :
    originalColumnKeep F reg σ (columnWitness F σ)=true := by
  simp only [originalColumnKeep,decide_eq_true_eq]
  exact witness_satisfies_all_true_old_tables F reg σ

theorem actual_column_flags_read_only_its_old_port
    (σ : W→Bool) (u : DOld F) (x y : DWire F→Bool) :
    oldColumnTruth F reg σ (.inr u) (fun p=>Sum.elim x y p.val)=
      oldRowTruth F reg σ (.inl u) (fun p=>y (edge p.val)) := by
  change oldRowTruth F reg σ (.inl u)
    ((fun p=>Sum.elim x y p.val)∘swappedPorts N (.inl u))=_
  apply congrArg (oldRowTruth F reg σ (.inl u))
  funext p
  obtain ⟨p,hp⟩ := p
  cases p
  · rfl
  · cases hp

end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.witness_satisfies_all_true_old_tables
#print axioms V8NativeMessage.N7LiteralSupport.original_columns_have_joint_word
#print axioms V8NativeMessage.N7LiteralSupport.actual_column_flags_read_only_its_old_port
