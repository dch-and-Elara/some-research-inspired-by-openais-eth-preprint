
import J2R43LiteralWholeMenuMenu

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 16
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

/-! Exact identification with the printed recursive executor. Different
precisions are transported by the existing agenda equality, not by
changing root center, binary probe, legal mode, or group. -/
namespace J2R43LiteralWholeMenu
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral
open J6R9PacketScopes J6ActiveRun J6R12Blueprint J6R11Blueprint J6R12Integral
open Paper5.D1Literal Paper5.HybridClosure J1PPrinted
open J9R15FrozenErasurePrecision

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {reg : ∀ v,GraphCutMoments.degree F v=3}
variable [Nonempty (MainClonedCNF.Port F)]
variable {f : ℤ[X]}

abbrev SourceReady (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
    (f : ℤ[X]) (σ : W→Bool) :=
  Ready (printedParams (f:=f) (ell:=1) (oldRowSize F))
    (sourceDelta (oldRowSize F)) (oldRowRoot F reg f σ)

def IsActualHighReply (P : RootPacking F reg f) (d : SourceReady F reg f (fun _=>false))
    (hf : f.Monic) (σ : W→Bool) (e : SourceReady F reg f σ)
    (x : PublicAddress F reg f P d) (v : Box f 1 (noncePrec F reg f x.1)) : Prop :=
  let root := oldRowRoot F reg f σ
  let sel := rootSel F reg f P σ
  let B := J6R12Blueprint.sourceBlueprint sel root hf
  let A := paddedRootAgendaEquiv F reg f P σ d e
  let w := A.symm x
  HEq (B.program.run (B.program.child root w)) v

theorem public_reply_is_actual (P : RootPacking F reg f) (d : SourceReady F reg f (fun _=>false))
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3≤sourceDelta (oldRowSize F))
    (hf : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (σ : W→Bool) (e : SourceReady F reg f σ) (x : PublicAddress F reg f P d) :
    IsActualHighReply P d hf σ e x (publicReply F reg f P d hf σ x) := by
  unfold IsActualHighReply
  dsimp only
  let A := paddedRootAgendaEquiv F reg f P σ d e
  let w := A.symm x
  have ha : A w=x := A.apply_symm_apply x
  have h := printedReply_matches_public F reg f P cfg hΔ hf hd d σ e w
  dsimp only at h
  have transfer (y y' : PublicAddress F reg f P d) (hy : y=y') :
      HEq (publicReply F reg f P d hf σ y) (publicReply F reg f P d hf σ y') := by
    cases hy
    rfl
  exact (heq_of_eq h).trans (transfer (A w) x ha)

theorem actual_completed_slots_zero (P : RootPacking F reg f)
    (d : SourceReady F reg f (fun _=>false))
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3≤sourceDelta (oldRowSize F))
    (hf : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (σ : W→Bool) (e : SourceReady F reg f σ) (x : PublicSlot F reg f P d)
    (depth : sourceQ F f≤(actualKept P x.1.val).card) :
    ∃ out : Fin 64→Box f 1 (noncePrec F reg f x.1),
      (∀ g,IsActualHighReply P d hf σ e ⟨x.1,x.2.1,x.2.2,g⟩ (out g)) ∧
      lowerBox (noncePrec F reg f x.1) (sourceQ F f) (sourceQ_fits x.1) f 1 (∏ g,out g)=0 := by
  refine ⟨fun g=>publicReply F reg f P d hf σ ⟨x.1,x.2.1,x.2.2,g⟩,?_,?_⟩
  · intro g
    exact public_reply_is_actual P d cfg hΔ hf hd σ e ⟨x.1,x.2.1,x.2.2,g⟩
  · exact literal_public_slot_erases P d hf hd σ x depth

theorem printed_actual_whole_menu (seed : RootPacking F reg f)
    (d : SourceReady F reg f (fun _=>false))
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3≤sourceDelta (oldRowSize F))
    (hf : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hU : 1≤J9PrintedSchedule.rootU (Nat.clog 2 (oldRowSize F))) (size : 320^2≤oldRowSize F) :
    ∃ Q : RootPacking F reg f,
      Q.rowLabel=seed.rowLabel ∧ Q.colLabel=seed.colLabel ∧ Q.copies=seed.copies ∧
      Fintype.card (DWire F)≤8*2^((printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0)*sourceQ F f ∧
      ∀ (σ : W→Bool) (x : PublicSlot F reg f Q d),
        let e := getReady cfg (oldRowRoot_stable F reg f σ hΔ) d.active
        ∃ out : Fin 64→Box f 1 (noncePrec F reg f x.1),
          (∀ g,IsActualHighReply Q d hf σ e ⟨x.1,x.2.1,x.2.2,g⟩ (out g)) ∧
          lowerBox (noncePrec F reg f x.1) (sourceQ F f) (sourceQ_fits x.1) f 1 (∏ g,out g)=0 := by
  obtain ⟨Q,hr,hc,hb,hscale,h⟩ := whole_printed_menu seed d hf hd hU size
  refine ⟨Q,hr,hc,hb,hscale,?_⟩
  intro σ x
  dsimp only
  refine ⟨fun g=>publicReply F reg f Q d hf σ ⟨x.1,x.2.1,x.2.2,g⟩,?_,h σ x⟩
  intro g
  exact public_reply_is_actual Q d cfg hΔ hf hd σ _ ⟨x.1,x.2.1,x.2.2,g⟩

#print axioms public_reply_is_actual
#print axioms actual_completed_slots_zero
#print axioms printed_actual_whole_menu
end
end J2R43LiteralWholeMenu
