import J6R33GeneratedChildSiteAtlas
import J6R12IntegralMenu
import J6R26DescriptorTreeNative
import J6R30ProducedGateRegistryHeterogeneous

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17500000
set_option maxRecDepth 2700

/-! Bind the event to the printed Appendix D centre, probe, menu
element and group, using the exact dependent tuple sent to the true
packet constructor. This theorem neither reuses root zero-mode bytes
nor changes the selected site chart after that event has been issued. -/
namespace J6R33GeneratedChildSite
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R27OriginalGate J6R30ProducedGateRegistry
open J6R26DescriptorTree J6R24MeteredRecursion J6R12Blueprint J6R11Blueprint J6R10Reachable
open J6R16ModeCost J6ActiveRun J6ActiveSchedule J6R9Recursive J6R12Integral J1PPrinted
open J6R32ChildResidentTransfer

section Source
variable {f : ℤ[X]} {ell Δ : ℕ} {S : Params (f:=f) (ell:=ell)}
variable {c : Call (PhysicalHost f ell)} (sel : Selector S Δ) (d : Ready S Δ c)
variable (t : Center S c) (z : Probe S c) (β : NativeMenu (shape S Δ sel) c t) (g : Fin 64)

abbrev physicalWidth := S.levelBits c.depth
abbrev realProbeCount := J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth)

noncomputable def activeMode (u : NativeMenu (shape S Δ sel) c t) :
    Legal (packing sel d) (centerIndex d t) (registerPrecision S c t) := by
  letI : Fintype (modeAt S Δ sel c t) := (shape S Δ sel).finiteMode c t
  letI : DecidableEq (modeAt S Δ sel c t) := (shape S Δ sel).decideMode c t
  let e := Equiv.cast (modeAt_eq S Δ sel d t)
  have w (m : modeAt S Δ sel c t) :
      siteWeight sel d t (e m) = weightAt S Δ sel c t m := by
    have H := weightAt_mode S Δ sel d t (e m)
    change weightAt S Δ sel c t (e.symm (e m))=_ at H
    rw [Equiv.symm_apply_apply] at H
    exact H.symm
  exact menuReindex (registerPrecision S c t) (register_positive d t) e
    (weightAt S Δ sel c t) (siteWeight sel d t) (weightAt_pos S Δ sel c t) w u

theorem active_mode_is_native_tuple :
    (activeMode sel d t β).val=siteTuple sel d ⟨t,z,β,g⟩ := rfl

variable {code tw bw q : ℕ}
  {fw : List (A1R10.Word (registerPrecision S c t))}
  {R : ChildResidents (physicalWidth (S:=S) (c:=c)) q}
variable (H : ResidentReceipt (packing sel d) (centerIndex d t) (registerPrecision S c t) R)

theorem all_active_pages
    (X : ActiveWords fw (q+1) tw bw)
    (clock : X.axis.length=(centerIndex d t).val)
    (hGroup : X.group.val=g.val) (hCentre : X.context.center=t.val)
    (hCode : X.context.codeWidth.val=code)
    (codePos : 0<code) (codeFit : 1+H.modes.length<2^code)
    (hβ : X.exponents.map Word.val=H.modes.map (fun m=>siteTuple sel d ⟨t,z,β,g⟩
      ((packet_mode_equiv (packing sel d).mask (centerIndex d t) (registerPrecision S c t)).symm m)))
    (hv : 0<ell) (fit : (centerIndex d t).val+1≤q+1)
    (hMod : A1R10.Modulus (registerPrecision S c t) (register_positive d t) fw=
      NativeProbeRing.liftPoly (registerPrecision S c t) f)
    (hZ : X.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
      (realProbeCount (S:=S) (c:=c)) d.fit z)) :
    Nonempty (AtlasReceipt (code:=code) H X (register_positive d t) hv fit hMod
      (sampleNode S f ell c d.fit t z) g (activeMode sel d t β)) ∧
      X.context.center=t.val ∧ X.context.codeWidth.val=code ∧
      (activeMode sel d t β).val=siteTuple sel d ⟨t,z,β,g⟩ := by
  refine ⟨?_,hCentre,hCode,active_mode_is_native_tuple sel d t z β g⟩
  exact actual_child_paged_atlas H X clock g hGroup codePos codeFit (activeMode sel d t β)
    hβ (register_positive d t) hv fit hMod d.fit z hZ
end Source

section Issuer
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep prec tc tz tm q tw bw : ℕ}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "iAt" => centerIndex (ticketReady T ticket) ticket.centerAt
local notation "pAt" => registerPrecision SP ticket.parent ticket.centerAt

theorem occurrence_precision_is_native : ticket.child.prec=pAt := rfl

/-- Register precision is read from the actual R26 receiving word;
modulus bytes and their exact interpretation are external inputs. -/
def issuedFrame (J : NativeJob T ticket port edge dep prec tc tz tm)
    (fw : List (A1R10.Word pAt)) (hOld : 0<fw.length)
    (hMod : A1R10.Modulus pAt (register_positive (ticketReady T ticket) ticket.centerAt) fw=
      NativeProbeRing.liftPoly pAt f) : FrameShape f prec :=
  ⟨pAt,(SP).levelBits ticket.parent.depth,q+1,fw,iAt,J.receiving,
    J.receiveExact.trans (occurrence_precision_is_native (ticket:=ticket)),
    register_positive (ticketReady T ticket) ticket.centerAt,hOld,hMod⟩

theorem issued_frame_retains_precision (J : NativeJob T ticket port edge dep prec tc tz tm)
    (fw : List (A1R10.Word pAt)) (hOld : 0<fw.length)
    (hMod : A1R10.Modulus pAt (register_positive (ticketReady T ticket) ticket.centerAt) fw=
      NativeProbeRing.liftPoly pAt f) :
    let F := issuedFrame (q:=q) J fw hOld hMod
    F.p=ticket.child.prec ∧ F.birth=J.receiving ∧ F.i=iAt := ⟨rfl,rfl,rfl⟩

variable {code : ℕ}
variable {fw : List (A1R10.Word (registerPrecision (printedParams (f:=f) (ell:=ell) s)
    ticket.parent ticket.centerAt))}
variable {R : ChildResidents ((printedParams (f:=f) (ell:=ell) s).levelBits ticket.parent.depth) q}
variable (H : ResidentReceipt (packing sel (ticketReady T ticket))
    (centerIndex (ticketReady T ticket) ticket.centerAt)
    (registerPrecision (printedParams (f:=f) (ell:=ell) s) ticket.parent ticket.centerAt) R)

theorem paid_native_occurrence_atlas (J : NativeJob T ticket port edge dep prec tc tz tm)
    (X : ActiveWords fw (q+1) tw bw) (hG : X.group=J.gWord)
    (clock : X.axis.length=(iAt).val)
    (hCentre : X.context.center=ticket.centerAt.val) (hCode : X.context.codeWidth.val=code)
    (codePos : 0<code) (codeFit : 1+H.modes.length<2^code)
    (hβ : X.exponents.map Word.val=H.modes.map (fun m=>siteTuple sel (ticketReady T ticket) ticket.slot.val
      ((packet_mode_equiv (packing sel (ticketReady T ticket)).mask iAt pAt).symm m)))
    (hv : 0<ell) (fit : (iAt).val+1≤q+1)
    (hMod : A1R10.Modulus pAt (register_positive (ticketReady T ticket) ticket.centerAt) fw=
      NativeProbeRing.liftPoly pAt f)
    (hZ : X.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
      (realProbeCount (S:=SP) (c:=ticket.parent)) (ticketReady T ticket).fit ticket.probeAt)) :
    Nonempty (AtlasReceipt (code:=code) H X (register_positive (ticketReady T ticket) ticket.centerAt)
      hv fit hMod (sampleNode SP f ell ticket.parent (ticketReady T ticket).fit ticket.centerAt ticket.probeAt)
      ticket.groupAt (activeMode sel (ticketReady T ticket) ticket.centerAt ticket.modeAt)) := by
  exact (all_active_pages sel (ticketReady T ticket) ticket.centerAt ticket.probeAt ticket.modeAt
      ticket.groupAt H X clock ((congrArg Word.val hG).trans J.gExact) hCentre hCode
      codePos codeFit hβ hv fit hMod hZ).1

/-- Each actual native mode slot has its word vector in the one paid
R25 batch. The program consumes that vector as an incoming event.
This statement does not grant random access to an entire past batch. -/
theorem paid_native_occurrence_event_exists (J : NativeJob T ticket port edge dep prec tc tz tm)
    (base : ActiveWords fw (q+1) tw bw) (hG : base.group=J.gWord)
    (clock : base.axis.length=(iAt).val)
    (hCentre : base.context.center=ticket.centerAt.val) (hCode : base.context.codeWidth.val=code)
    (codePos : 0<code) (codeFit : 1+H.modes.length<2^code)
    (hv : 0<ell) (fit : (iAt).val+1≤q+1)
    (hMod : A1R10.Modulus pAt (register_positive (ticketReady T ticket) ticket.centerAt) fw=
      NativeProbeRing.liftPoly pAt f)
    (hZ : base.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
      (realProbeCount (S:=SP) (c:=ticket.parent)) (ticketReady T ticket).fit ticket.probeAt)) :
    let hp := register_positive (ticketReady T ticket) ticket.centerAt
    ∃ ev ∈ (emitted H hp).result.vectors,
      Nonempty (AtlasReceipt (code:=code) H {base with exponents:=ev} hp hv fit hMod
        (sampleNode SP f ell ticket.parent (ticketReady T ticket).fit ticket.centerAt ticket.probeAt)
        ticket.groupAt (activeMode sel (ticketReady T ticket) ticket.centerAt ticket.modeAt)) := by
  let hp := register_positive (ticketReady T ticket) ticket.centerAt
  let β := activeMode sel (ticketReady T ticket) ticket.centerAt ticket.modeAt
  obtain ⟨ev,belongs,read⟩ := every_legal_mode_emitted H hp β
  exact ⟨ev,belongs,paid_native_occurrence_atlas H J {base with exponents:=ev}
    hG clock hCentre hCode codePos codeFit read hv fit hMod hZ⟩
end Issuer

#print axioms active_mode_is_native_tuple
#print axioms all_active_pages
#print axioms occurrence_precision_is_native
#print axioms issued_frame_retains_precision
#print axioms paid_native_occurrence_atlas
#print axioms paid_native_occurrence_event_exists
end J6R33GeneratedChildSite
