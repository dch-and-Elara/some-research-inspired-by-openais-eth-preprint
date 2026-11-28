import V8NativeMessageN7LiteralSupportComponentOppositeSource
import V8NativeMessageN7LiteralSupportOppositeParity
import V8NativeMessageN7LiteralSupportComponentIsolated
import V8NativeMessageN7HighBoundReceipt

/-! All the original old-column pins must be matched if a real
opposite zero-mode parity slot gives the exterior matching target. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles J6R9Recursive DenominatorBudget
open J6ActiveRun J6R12Blueprint J6R11Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000
set_option maxRecDepth 2600
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v,GraphCutMoments.degree E v=3)
variable (loopless : ∀ v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "hF" => replaced_cubic E baseCubic loopless
variable {f : ℤ[X]}
local notation "SP" => printedParams (f:=f) (ell:=1) (oldRowSize F)

theorem native_old_column_exterior_pair_cannot_split
    (P : ColumnPacking (replacedEdges E baseCubic)
      (replaced_cubic E baseCubic loopless) (f:=f))
    (d : ColumnReady F hF (f:=f))
    (t : ColumnCenter F hF (f:=f)) (i : Fin ((SP).levelBits 0))
    (hv : padicValInt 2 t.val=i.val)
    (z : Residue f 1 (oppositePrintedPrec F hF t))
    (hf : f.Monic) (hd : 0<f.natDegree)
    (correct : ∀ σ,
      observe f (oppositePrintedPrec F hF t) 1 (opposite_printed_precision_positive F hF t)
        (originalOppositeSlot F hF P d t i hv z 0 hf σ)=UD E baseCubic (Residue f 1 1) σ)
    (e : E) :
    Connected P t.val (oldUnaryColumn F (seat E baseCubic e false))
      (oldUnaryColumn F (seat E baseCubic e true)) := by
  have nz : (1:Residue f 1 1)≠0 := by
    intro h
    have bad := (V8NativeMessage.N7HighBound.integer_box_zero_iff_of_height 1 (by decide)
      f hf hd 1 (by decide)).mp (by simpa only [Int.cast_one] using h)
    exact (by decide : (1:ℤ)≠0) bad
  letI : Nontrivial (Residue f 1 1) := nontrivial_of_ne (1:Residue f 1 1) 0 nz
  refine true_old_column_exterior_pair_in_same_wiring_component E baseCubic loopless P
    i (centerNonzero t) hv (public_center_in_grid F hF (show PublicCenter F hF f from t))
    (oppositePrintedParityMap F hF t) (by simpa only [pow_one] using J6R10Integral.box_two_nil 1 f 1)
    ?_ e
  intro σ
  exact (literal_opposite_zero_mode_same_parity_at_any_probe F hF P d t i hv z hf hd σ).symm.trans
    (correct σ)

theorem native_old_column_parity_needs_all_original_pins
    (P : ColumnPacking (replacedEdges E baseCubic)
      (replaced_cubic E baseCubic loopless) (f:=f))
    (d : ColumnReady F hF (f:=f))
    (t : ColumnCenter F hF (f:=f)) (i : Fin ((SP).levelBits 0))
    (hv : padicValInt 2 t.val=i.val)
    (z : Residue f 1 (oppositePrintedPrec F hF t))
    (hf : f.Monic) (hd : 0<f.natDegree)
    (correct : ∀ σ,
      observe f (oppositePrintedPrec F hF t) 1 (opposite_printed_precision_positive F hF t)
        (originalOppositeSlot F hF P d t i hv z 0 hf σ)=UD E baseCubic (Residue f 1 1) σ) :
    ∀ v : TriVertex V,∃ r,Matches P t.val r (sourceUnaryWire F v) := by
  intro v
  obtain ⟨⟨e,b⟩,rfl⟩ := (exteriorPort E baseCubic).surjective v
  by_contra! absent
  have conn := native_old_column_exterior_pair_cannot_split E baseCubic loopless P d t i hv z hf hd correct e
  have distinct : oldUnaryColumn F (seat E baseCubic e false) ≠
      oldUnaryColumn F (seat E baseCubic e true) := by
    intro h
    have same := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))
    have samePair := (exteriorPort E baseCubic).injective same
    exact Bool.noConfusion (congrArg Prod.snd samePair)
  cases b
  · exact distinct (original_unmatched_old_column_is_isolated F hF P t.val _ absent conn).symm
  · exact distinct (original_unmatched_old_column_is_isolated F hF P t.val _ absent
      (Relation.EqvGen.symm _ _ conn))

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.native_old_column_exterior_pair_cannot_split
#print axioms V8NativeMessage.N7LiteralSupport.native_old_column_parity_needs_all_original_pins
