import J6R111SelectedGroup

namespace J6R111SelectedGroup
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R34ChildPath J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R52FreshExterior J6R57PublicRequest J6R54PublicFamily
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R28GeneratedRootFrame J6R14ZeroMode J6R34OfficialGateway A1R12
open J6R68ActiveInputs.Sweep J6R75OuterTime J6R19Retained J1PPrinted

open A1R10
open AOracleMachineTimeTape
open J6ActiveRun
open J6OrientedHostEval
open J6R10Reachable
open J6R11Blueprint
open J6R11Repack
open J6R12Blueprint
open J6R16ModeCost
open J6R21Ancestor
open J6R22Active
open J6R22RootReadout
open J6R25StableCensus
open J6R26DescriptorTree
open J6R30ProducedGateRegistry
open J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs
open J6R33OriginalJ6
open J6R35GatewayPreparation
open J6R35RootOrigins
open J6R36SharedGateway
open J6R37StructuredRoot
open J6R41StructuredAllPaths
open J6R48DFS
open J6R49Cost
open J6R55CachedLedger
open J6R56PrintedExponent
open J6R62ActivePrep
open J6R63Active
open J6R64Active
open J6R66.BootPeak
open J6R66Active
open J6R67UnifiedRate
open J6R68AbsolutePrescribed
open J6R68ActiveInputs
open J6R9Recursive

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 23000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (prior : (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))) (R : RawGroupPlans D S pad prior cfg rate cw)
variable (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
variable (setups : ∀ (i : (J6Recovery.Addr m)) (j : (Fin (literalDegree m native+1))) (g : Fin 64),
  PaidSetupForPlan D S pad prior (sourceRow (W:=W) D i j g) (R i j g))

def reindexPaidSetup {a b : Entry D.mark m native tc tj tw} (e : a=b)
    {A : RawGroupPlan D S pad prior a cfg rate cw}
    (Q : PaidSetupForPlan D S pad prior a A) :
    PaidSetupForPlan D S pad prior b (e ▸ A) := by
  subst b
  exact Q
def paidSelectedAtHead (i : (J6Recovery.Addr m)) (j : (Fin (literalDegree m native+1))) (g : Fin 64)
    (H : ExactHead m native tc tj tw i j) (same : H=(prepareHead W i j).result) :
    Meter (Block (actualGroupFrame D S pad prior R i j g) ell) :=
  let addressed := emitEntry D.mark (i,j) H g
  have eq : addressed.result=sourceRow (W:=W) D i j g := by subst H; rfl
  let u : {r : Entry D.mark m native tc tj tw // r=sourceRow (W:=W) D i j g} := ⟨addressed.result,eq⟩
  let v : {r : Entry D.mark m native tc tj tw // r=sourceRow (W:=W) D i j g} :=
    ⟨sourceRow (W:=W) D i j g,rfl⟩
  have seen : u.val∈S.requests.rows := by
    change addressed.result∈S.requests.rows
    rw [eq]
    exact canonical_source_row_is_resident D S i j g
  let rowPlan : RawGroupPlan D S pad prior u.val cfg rate cw := u.property.symm ▸ R i j g
  let chosen : PaidSetupForPlan D S pad prior u.val rowPlan := reindexPaidSetup D S pad prior u.property.symm (setups i j g)
  let localRun : Meter (sameRowFamily D S pad prior R i j g u) :=
    actualPaidOnWrittenRow D S pad prior sync reserved u.val seen rowPlan chosen
  let delivered := transportPaid (sameRowFamily D S pad prior R i j g) (show u=v from Subtype.ext eq) localRun
  ⟨delivered.result,addressed.steps+delivered.steps+3⟩

abbrev selectedGroupExtra (i : (J6Recovery.Addr m)) (j : (Fin (literalDegree m native+1))) (g : Fin 64) : ℕ :=
  actualSelectedSetupFee D S pad prior sync reserved (sourceRow (W:=W) D i j g)
    (canonical_source_row_is_resident D S i j g) (R i j g) (setups i j g)

theorem actual_emitted_group_has_only_the_paid_setup_delta (i : (J6Recovery.Addr m)) (j : (Fin (literalDegree m native+1))) (g : Fin 64)
    (H : ExactHead m native tc tj tw i j) (same : H=(prepareHead W i j).result) :
    Delta (paidSelectedAtHead D S pad prior R sync reserved setups i j g H same)
      (paidSourceGroup D S pad prior R sync reserved i j g H same)
      (selectedGroupExtra D S pad prior R sync reserved setups i j g) := by
  subst H
  let e := emitEntry D.mark (i,j) (prepareHead W i j).result g
  let r := sourceRow (W:=W) D i j g
  let h := canonical_source_row_is_resident D S i j g
  let old := paidOnWrittenRow D S pad prior sync reserved r h (R i j g)
  let new := actualPaidOnWrittenRow D S pad prior sync reserved r h (R i j g) (setups i j g)
  have same := actual_written_row_uses_its_paid_setup_exactly_once
    D S pad prior sync reserved r h (R i j g) (setups i j g)
  dsimp only at same
  change Delta ⟨new.result,e.steps+new.steps+3⟩ ⟨old.result,e.steps+old.steps+3⟩ _
  have hs : new.steps=old.steps+selectedGroupExtra D S pad prior R sync reserved setups i j g := same.2
  exact ⟨same.1,by dsimp only; rw [hs]; omega⟩

variable (frame : Frame f (J6SourcePrecision.printed m base)) (hv : 0<ell)

def paidSelectedSlot : SlotProgram (ell:=ell) (F:=frame) G :=
  fun i j _ =>
    let E := SiteFrame G ell frame i
    let H := prepareHead W i j
    let collect := foldM E.hp E.sizePos hv (fun g : Fin 64=>
      frameCopy D.hf (actualGroupFrame D S pad prior R i j g) E
        (paidSelectedAtHead D S pad prior R sync reserved setups i j g H.result rfl)) (groupOrder 64)
    ⟨collect.result,H.steps+collect.steps+3⟩

theorem actual_selected_slot_charges_its_64_real_setups
    (i : (J6Recovery.Addr m)) (j : (Fin (literalDegree m native+1))) (message : List Bool) :
    Delta (paidSelectedSlot D S pad prior R sync reserved setups frame hv i j message)
      (paidRawSlot D S pad prior R sync reserved frame hv i j message)
      (∑ g : Fin 64,selectedGroupExtra D S pad prior R sync reserved setups i j g) := by
  let E := SiteFrame G ell frame i
  let H := prepareHead W i j
  let fst := fun g : Fin 64=>paidSelectedAtHead D S pad prior R sync reserved setups i j g H.result rfl
  let snd := fun g : Fin 64=>paidSourceGroup D S pad prior R sync reserved i j g H.result rfl
  let read := fun g : Fin 64=>frameCopy D.hf (actualGroupFrame D S pad prior R i j g) E (fst g)
  let old := fun g : Fin 64=>frameCopy D.hf (actualGroupFrame D S pad prior R i j g) E (snd g)
  let extra := selectedGroupExtra D S pad prior R sync reserved setups i j
  have hd (g : Fin 64) : Delta (read g) (old g) (extra g) := by
    have h : Delta (fst g) (snd g) (extra g) :=
      actual_emitted_group_has_only_the_paid_setup_delta D S pad prior R sync reserved setups i j g H.result rfl
    have val := h.value
    have pay := h.fee
    unfold read old frameCopy
    dsimp only
    rw [val,pay]
    exact ⟨rfl,by dsimp only; omega⟩
  have h := product_delta E.hp E.sizePos hv read old extra (groupOrder 64) (fun g _=>hd g)
  have hs : ((groupOrder 64).map extra).sum=(∑ g : Fin 64,extra g) := by
    rw [groupOrder,List.map_ofFn,List.sum_ofFn]
    rfl
  let a := foldM E.hp E.sizePos hv read (groupOrder 64)
  let b := foldM E.hp E.sizePos hv old (groupOrder 64)
  have H0 : a.result=b.result := h.value
  have H1 : a.steps=b.steps+(∑ g : Fin 64,extra g) := h.fee.trans (congrArg (b.steps+·) hs)
  change Delta ⟨a.result,H.steps+a.steps+3⟩ ⟨b.result,H.steps+b.steps+3⟩
    (∑ g : Fin 64,extra g)
  exact ⟨H0,by dsimp only; omega⟩

#print axioms actual_emitted_group_has_only_the_paid_setup_delta
#print axioms actual_selected_slot_charges_its_64_real_setups
end
end J6R111SelectedGroup
