import J6R51LeafWhole
import J6R51OnlineDepth

/-! Combine the generated depth-issuance stack with the actual paid
terminal implementation of the same online source runner. Do not
take a ReadyOnStack or a LeafAgreement input. -/
namespace J6R51Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R27OriginalGate J6R9PacketScopes
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R34RootAtlas J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R22Active J6R35RootOrigins J6R48Leaf J6R49Leaf
open J6R9Recursive J6R10Reachable J6R24MeteredRecursion J6R21Leaf J6R16ModeCost
open J6R26DescriptorTree J6R34ChildPath J6R25PreparedSupply
open J6R15ModeCost J6R48DFS J6R50Leaf J6R50SourceProducer J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 47000000
set_option maxRecDepth 4800

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {V : Type} [Fintype V]
variable {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co d edgew tc tj key prec tw bw rate : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
local notation "ext" => exteriorChild G ell X.centre X.sample X.group
local notation "pg" => pageKeyWidth m+pad
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine P key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (rootOrd : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (data : ∀ {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
  (site : StoredSite P v key prec tw bw (pageKeyWidth m+pad)),ResidentLeafData site)

theorem actual_online_root_from_depth_issuance
    (initial : PageBank f ell key prec tw bw pg)
    (rootLive : IsLive (X.seed pad) initial) (chart : LoopCharts X pad M basePos data)
    (retire : PageJob f ell key prec tw bw pg→ℕ)
    (offset : ℕ) (current : J6R15ModeCost.Word key) (pos : 0<key)
    (cap : offset+pathLimit s C<2^key) (rootKey : current.val=offset+1)
    (sync : initial.synced) (parentTags : ∀ a∈initial.headers,a.id.val≤offset+1)
    (startIds : ∀ w, (M.initial w).result.birth.job.identifier=(increment current).result)
    (loadedIds : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c)
      (u : (Plan sel).Slot c) (w : (Plan sel).Slot ((Plan sel).child c u)),
      (M.demand (sourceState M p u) w).result.event.issued =
        increment (sourceState M p u).birth.job.identifier) :
    let R := replaceTerminalFields X pad M basePos rootOrd data
    let out := runRoot R retire initial
    (P.frame (Path.root : Path sel ext ext).reached).decode out.result.1=
        (sourceBlueprint sel ext X.hf).program.run ext ∧ out.result.2=initial ∧
    (∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (u : (Plan sel).Slot c),
      (borns R p u).job.identifier.val=offset+((Plan sel).child c u).depth) ∧
    (∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c)
      (u : (Plan sel).Slot c) (w : (Plan sel).Slot ((Plan sel).child c u)),
      (R.demand (sourceState R p u) w).result.event.issued.steps=13*key+4) := by
  have height : (ext).depth=1 := rfl
  have fit : (ext).depth≤pathLimit s C := by
    rw [height]
    unfold pathLimit
    omega
  have hk : current.val=offset+(ext).depth := rootKey.trans (congrArg (offset+·) height.symm)
  have hb (a : DirRow key) (ha : a∈initial.headers) : a.id.val≤offset+(ext).depth := by
    rw [height]
    exact parentTags a ha
  obtain ⟨ready,labels,costs⟩ := online_depth_issuance_and_stack M initial offset current pos cap fit hk
    sync hb startIds loadedIds
  have run := actual_online_root_with_proved_terminal_fields X pad M basePos rootOrd data
    initial rootLive ready chart retire
  refine ⟨run.1,run.2,?_,?_⟩
  · intro c p w
    let G := replaceTerminalFields X pad M basePos rootOrd data
    change (sourceState G p w).birth.job.identifier.val=_
    rw [show sourceState G p w=sourceState M p w from
      replacement_keeps_actual_source_state X pad M basePos rootOrd data p w]
    exact labels p w
  · intro c p u w
    let G := replaceTerminalFields X pad M basePos rootOrd data
    change (G.demand (sourceState G p u) w).result.event.issued.steps=_
    rw [show sourceState G p u=sourceState M p u from
      replacement_keeps_actual_source_state X pad M basePos rootOrd data p u]
    exact costs p u w

#print axioms actual_online_root_from_depth_issuance
end
end J6R51Leaf
