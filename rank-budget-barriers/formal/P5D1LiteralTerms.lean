import P5D1LiteralPublicSum
import P5D1LiteralField
import GroupProducts

/-! Convert the common D1 agenda to the exact E1 group-product syntax.
The factor per group really is an actual received child value in the
rational coefficient field, not an arbitrary replacement contraction. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun J6ActiveSchedule
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral GroupProducts

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable (f : ℤ[X])
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F cubic f (fun _ => false))
variable (P : RootPacking F cubic f)

noncomputable def rootKept : Finset (Fin ((S).levelBits 0)) :=
  Finset.univ.filter (fun i => i.val < (S).levelWidth 0)

theorem publicIndex_mem (d : Ready S Δ r*) (t : PublicCenter F cubic f) :
    PublicIndex F cubic f d t ∈ rootKept F f := by
  have ht := active_order_pos ((S).levelBits 0) (r*).edges ((S).levelWidth 0) t.val t.property
  have hi : padicValInt 2 t.val < (S).levelWidth 0 := by
    unfold order at ht
    exact Nat.sub_pos_iff_lt.mp (Nat.pos_of_ne_zero (by
      intro h
      rw [h,mul_zero] at ht
      exact (Nat.lt_irrefl 0) ht))
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩

noncomputable abbrev rootLabels (v : W) (i : rootKept F f) : Fin 64 :=
  P.rowLabel (.inr (.inl v)) i.val

noncomputable def agendaGroupTerm (d : Ready S Δ r*) (hf : f.Monic) (u : PublicSlot F cubic f P d) :
    GroupTerm (rootLabels F cubic f P) (RatScalar f) where
  coordinate := ⟨PublicIndex F cubic f d u.1,publicIndex_mem F cubic f d u.1⟩
  coeff := zeroCoordinate (RatScalar f) (publicMenuWeight F cubic f d u.1 u.2.1)
  factor g bits := sourceFieldMap f
    (representative (registerPrecision S r* u.1) f 1
      (publicReply F cubic f P d hf
        (extendSign F cubic P (PublicIndex F cubic f d u.1) g bits)
        ⟨u.1,u.2.1,u.2.2,g⟩))

theorem agendaGroupTerm_value (d : Ready S Δ r*) (hf : f.Monic) (u : PublicSlot F cubic f P d)
    (σ : W → Bool) :
    (agendaGroupTerm F cubic f P d hf u).value σ =
      zeroCoordinate (RatScalar f) (publicTerm F cubic f P d hf σ u) := by
  unfold GroupTerm.value publicTerm
  rw [map_mul,map_prod]
  apply congrArg (fun z => zeroCoordinate (RatScalar f)
    (publicMenuWeight F cubic f d u.1 u.2.1) * z)
  apply Finset.prod_congr rfl
  intro g _
  change sourceFieldMap f
    (representative (registerPrecision S r* u.1) f 1
      (publicReply F cubic f P d hf
        (extendSign F cubic P (PublicIndex F cubic f d u.1) g (fun v => σ v.val))
        ⟨u.1,u.2.1,u.2.2,g⟩)) =
      sourceFieldMap f (representative (registerPrecision S r* u.1) f 1
      (publicReply F cubic f P d hf σ ⟨u.1,u.2.1,u.2.2,g⟩))
  apply congrArg (fun b => sourceFieldMap f (representative (registerPrecision S r* u.1) f 1 b))
  apply publicReply_local
  intro v
  simp only [extendSign,dif_pos v.property]

theorem sum_agendaGroupTerm_value (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool) :
    (∑ u : PublicSlot F cubic f P d, (agendaGroupTerm F cubic f P d hf u).value σ) =
      zeroCoordinate (RatScalar f) (publicMenuSum F cubic f P d hf σ) := by
  simp_rw [agendaGroupTerm_value F cubic f P d hf]
  unfold publicMenuSum
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_prod_type,map_sum]

/-- Retained root labels are literally the old pin-row coordinates, not
an independently chosen partition used only for the rank proof. -/
theorem same_rootLabels_as_E1 {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (hreg : ∀ v, GraphCutMoments.degree E v=3)
    (hloop : ∀ v,(v,v)∉E)
    (Q : RootPacking (replacedEdges E hreg) (replaced_cubic E hreg hloop) f) :
    rootLabels (replacedEdges E hreg) (replaced_cubic E hreg hloop) f Q =
      DPinLabels E hreg hloop Q (rootKept (replacedEdges E hreg) f) := rfl

#print axioms publicIndex_mem
#print axioms agendaGroupTerm_value
#print axioms sum_agendaGroupTerm_value
#print axioms same_rootLabels_as_E1
end Paper5.D1Literal
