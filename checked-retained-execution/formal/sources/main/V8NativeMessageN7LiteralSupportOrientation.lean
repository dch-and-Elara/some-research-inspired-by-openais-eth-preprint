import V8NativeMessageN7PublicShift

/-! The other source orientation uses the identical four-clone
incidence wires. This is a typed transposition of the true binary
tables, not a newly chosen network which merely has the same sizes. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R11Blueprint
open J6ActiveRun J6R12Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000
set_option maxRecDepth 2200
noncomputable section

section Transpose
variable {E A B : Type} (N : Network E A B)

def swapNetwork : Network E B A :=
  ⟨N.col,N.row⟩

private theorem swapped_owner (p : Port E) :
    owner (swapNetwork N) ((Equiv.sumComm E E) p)=
      (Equiv.sumComm A B) (owner N p) := by
  cases p <;> rfl

def swappedPorts (v : A⊕B) :
    ParentPorts N v ≃ ParentPorts (swapNetwork N) ((Equiv.sumComm A B) v) where
  toFun q := ⟨(Equiv.sumComm E E) q.val,(swapped_owner N q.val).trans
    (congrArg (Equiv.sumComm A B) q.property)⟩
  invFun q := ⟨(Equiv.sumComm E E).symm q.val,by
    apply (Equiv.sumComm A B).injective
    rw [←swapped_owner,Equiv.apply_symm_apply,q.property]⟩
  left_inv q := Subtype.ext ((Equiv.sumComm E E).symm_apply_apply q.val)
  right_inv q := Subtype.ext ((Equiv.sumComm E E).apply_symm_apply q.val)

/-- Implement all old clause/equality/unary tables on the real
oppositely oriented scopes. Their old local arguments are not projected
through the deformation: this is the underlying source host. -/
def swappedFlags (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    ∀ v : B⊕A,(ParentPorts (swapNetwork N) v→Bool)→Bool
  | .inl b,x => flags (.inr b) (x∘swappedPorts N (.inr b))
  | .inr a,x => flags (.inl a) (x∘swappedPorts N (.inl a))

theorem swapped_flags_same_local_table
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)
    (v : A⊕B) (x : ParentPorts N v→Bool) :
    swappedFlags N flags ((Equiv.sumComm A B) v) (x∘(swappedPorts N v).symm)=flags v x := by
  cases v with
  | inl a =>
    change flags (.inl a) ((x∘(swappedPorts N (.inl a)).symm)∘swappedPorts N (.inl a))=_
    apply congrArg (flags (.inl a))
    funext q
    simp [Function.comp_def]
  | inr b =>
    change flags (.inr b) ((x∘(swappedPorts N (.inr b)).symm)∘swappedPorts N (.inr b))=_
    apply congrArg (flags (.inr b))
    funext q
    simp [Function.comp_def]

end Transpose

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Delta" => (sourceDelta (oldRowSize F))
local notation "N" => (dNetwork F reg)

abbrev oldColumnNetwork := swapNetwork N

def oldColumnTruth (σ : W→Bool) :=
  swappedFlags N (oldRowTruth F reg σ)

def oldColumnFile (f : ℤ[X]) (σ : W→Bool) : EntryFile f 1 (oldColumnNetwork F reg) :=
  V8PooledMenu.binaryFile f (4*Fintype.card W+1) (oldColumnTruth F reg σ)

def oldColumnRoot (f : ℤ[X]) (σ : W→Bool) : Call (PhysicalHost f 1) :=
  ⟨physicalHost (oldColumnNetwork F reg) (oldColumnFile F reg f σ),
    0,Fintype.card (DWire F),4*Fintype.card W+1⟩

theorem opposite_orientation_same_source_sizes (σ : W→Bool) :
    (oldColumnRoot F reg f σ).edges=24*Fintype.card W ∧
      (oldColumnRoot F reg f σ).prec=4*Fintype.card W+1 ∧
      (oldColumnRoot F reg f σ).depth=0 :=
  ⟨d_physical_wire_count F reg,rfl,rfl⟩

theorem subdivision_row_literal (σ : W→Bool) (p : MainClonedCNF.Port F)
    (x : ParentPorts (oldColumnNetwork F reg) (.inl p)→Bool) :
    oldColumnTruth F reg σ (.inl p) x =
      decide (x ⟨.inl (p,false),rfl⟩=x ⟨.inl (p,true),rfl⟩) := rfl

theorem unary_column_literal (σ : W→Bool) (v : W)
    (x : ParentPorts (oldColumnNetwork F reg) (.inr (.inr (.inl v)))→Bool) :
    oldColumnTruth F reg σ (.inr (.inr (.inl v))) x =
      decide (x ⟨.inr (.inl v,true),rfl⟩=σ v) := rfl

local notation "rstar" => (oldColumnRoot F reg f (fun _=>false))
abbrev ColumnPacking := PhysicalPacking (oldColumnNetwork F reg) ((S).levelBits 0) (Fin 64)
abbrev ColumnReady := Ready S Delta rstar
abbrev ColumnCenter := Center S rstar

def originalOppositeSlot (P : ColumnPacking F reg (f:=f))
    (_d : ColumnReady F reg (f:=f)) (t : ColumnCenter F reg (f:=f))
    (pIndex : Fin ((S).levelBits 0)) (hv : padicValInt 2 t.val=pIndex.val)
    (z : Residue f 1 (registerPrecision S rstar t))
    (β : J6R9PacketScopes.Mode pIndex (registerPrecision S rstar t) P.mask→₀ℕ)
    (hf : f.Monic) (σ : W→Bool) : Residue f 1 (registerPrecision S rstar t) :=
  V8PooledMenu.slot P pIndex (centerNonzero t) hv (registerPrecision S rstar t)
    (J6R10Integral.box_two_nil _ f 1) z (oldColumnFile F reg f σ) hf β

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.swappedPorts
#print axioms V8NativeMessage.N7LiteralSupport.swapped_flags_same_local_table
#print axioms V8NativeMessage.N7LiteralSupport.opposite_orientation_same_source_sizes
#print axioms V8NativeMessage.N7LiteralSupport.subdivision_row_literal
#print axioms V8NativeMessage.N7LiteralSupport.unary_column_literal
#print axioms V8NativeMessage.N7LiteralSupport.originalOppositeSlot
