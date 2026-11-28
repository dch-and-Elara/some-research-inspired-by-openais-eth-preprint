import V8NativeMessageN7LiteralSupportCertificateCompose
import V8NativeMessageN7LiteralSupportComponentLocal
import V8NativeMessageN7LiteralSupportComponentColumn
import V8NativeMessageN6DTarget

/-! Sufficiency for the actual original two orientations: correctness
on the finite local sign words certifies the zero-mode parity target
for every global sign word on the same four-clone host. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles DenominatorBudget
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000
set_option maxRecDepth 2500
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v,GraphCutMoments.degree E v=3)
variable (loopless : ∀ v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "hF" => replaced_cubic E baseCubic loopless
variable {a : ℕ} {K R : Type} [Fintype K] [CommRing R]

theorem old_row_native_component_local_certificate_suffices
    (P : PhysicalPacking (dNetwork (replacedEdges E baseCubic)
      (replaced_cubic E baseCubic loopless)) a (Fin 64))
    (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (mem : t∈P1DyadicGrid.grid a) (φ : TwoLocal→+*R) (h2 : (2:R)=0)
    (color : DOld F⊕MainClonedCNF.Port F→K)
    (uncut : ∀{r q},Matches P t r q→color (.inl ((dNetwork F hF).row r))=
      color (.inr ((dNetwork F hF).col q)))
    (co : ∀ e : E,color (oldUnaryVertex F (seat E baseCubic e false))=
      color (oldUnaryVertex F (seat E baseCubic e true)))
    (check : ∀ k (x : Fiber (fun v=>color (oldUnaryVertex F v)) k→Bool),
      let σ := fillFiber (fun v=>color (oldUnaryVertex F v)) k true x
      (literalComponentFactors P t color (oldRowTruth F hF σ) k : R) =
        localPairValue (fun v=>color (oldUnaryVertex F v))
          (fun e : E=>seat E baseCubic e false) (fun e : E=>seat E baseCubic e true) σ k)
    (σ : TriVertex V→Bool) :
    φ (exactZero P i t (oldRowTruth F hF σ))=UD E baseCubic R σ := by
  rw [factor_actual_parity_wiring P i ht hv mem φ h2 color uncut]
  exact verified_component_local_tables_compose (fun v=>color (oldUnaryVertex F v))
    (fun e : E=>seat E baseCubic e false) (fun e : E=>seat E baseCubic e true) co
    (fun k w=>literalComponentFactors P t color (oldRowTruth F hF w) k)
    (actual_old_component_factor_is_sign_local F hF P t color) check σ

theorem old_column_native_component_local_certificate_suffices
    (P : PhysicalPacking (oldColumnNetwork (replacedEdges E baseCubic)
      (replaced_cubic E baseCubic loopless)) a (Fin 64))
    (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (mem : t∈P1DyadicGrid.grid a) (φ : TwoLocal→+*R) (h2 : (2:R)=0)
    (color : MainClonedCNF.Port F⊕DOld F→K)
    (uncut : ∀{r q},Matches P t r q→color (.inl ((oldColumnNetwork F hF).row r))=
      color (.inr ((oldColumnNetwork F hF).col q)))
    (co : ∀ e : E,color (oldUnaryColumn F (seat E baseCubic e false))=
      color (oldUnaryColumn F (seat E baseCubic e true)))
    (check : ∀ k (x : Fiber (fun v=>color (oldUnaryColumn F v)) k→Bool),
      let σ := fillFiber (fun v=>color (oldUnaryColumn F v)) k true x
      (literalComponentFactors P t color (oldColumnTruth F hF σ) k : R) =
        localPairValue (fun v=>color (oldUnaryColumn F v))
          (fun e : E=>seat E baseCubic e false) (fun e : E=>seat E baseCubic e true) σ k)
    (σ : TriVertex V→Bool) :
    φ (exactZero P i t (oldColumnTruth F hF σ))=UD E baseCubic R σ := by
  rw [factor_actual_parity_wiring P i ht hv mem φ h2 color uncut]
  exact verified_component_local_tables_compose (fun v=>color (oldUnaryColumn F v))
    (fun e : E=>seat E baseCubic e false) (fun e : E=>seat E baseCubic e true) co
    (fun k w=>literalComponentFactors P t color (oldColumnTruth F hF w) k)
    (actual_old_column_component_factors_are_sign_local F hF P t color) check σ

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.old_row_native_component_local_certificate_suffices
#print axioms V8NativeMessage.N7LiteralSupport.old_column_native_component_local_certificate_suffices
