import J6R75OuterTimeCount
import J6R75OuterTimeStart
import J6R75OuterTimeBill

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Compose the concrete literal group, public-slot and signed readout
tariffs. The only route-dependent caps here are on the same physical
publication and the same measured R68 core, not black-box reply meters. -/
namespace J6R75OuterTime
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath J6R35GatewayPreparation
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R66.BootPeak
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R36SharedGateway J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R34OfficialGateway J6R68AbsolutePrescribed
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6OrientedHostEval
open J6R63Active J6R62ActivePrep J6R14ZeroMode

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))


local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))


variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (R : RawGroupPlans D S pad B cfg rate cw)
variable (sync : B.synced) (reserved : ∀ x∈B.headers,x.id.bits.take kp≠D.mark.bits)
variable (frame : Frame f (J6SourcePrecision.printed m base))
variable (hv : 0<ell)


theorem printed_outer_slot_has_its_own_group_sum
    (i : Centre) (j : Sample) (raw : List Bool) :
    let head := prepareHead W i j
    let p := (exteriorChild G ell i j (0:Fin 64)).prec
    let E := SiteFrame G ell frame i
    (paidRawSlot D S pad B R sync reserved frame hv i j raw).steps ≤ head.steps+(∑ g : Fin 64,(paidSourceGroup D S pad B R sync reserved i j g head.result rfl).steps)+
        64*(boxFee f.natDegree ell p p+4)+tupleExtra E.words.length ell p 64+3 := by
  let head := prepareHead W i j
  let E := SiteFrame G ell frame i
  let p := (exteriorChild G ell i j (0:Fin 64)).prec
  let group := fun g=>verifiedSourceGroup D S pad B R sync reserved i j g head.result rfl
  let read := fun g=>groupOnSite G D.hf frame i j g (group g)
  let complete := completedGroups G D.hf frame hv i j group
  have agg := (completed_groups_exact G D.hf frame hv i j group).2
  have composed : complete.steps ≤ bill read (groupOrder 64)+tupleExtra E.words.length ell p 64 := agg
  have byGroup : bill read (groupOrder 64) ≤ (∑ g : Fin 64,(group g).run.steps)+64*(boxFee f.natDegree ell p p+4) := by
    unfold bill groupOrder
    rw [List.map_ofFn,List.sum_ofFn]
    simp only [Function.comp_apply]
    calc
      _ ≤ ∑ g : Fin 64,((group g).run.steps+(boxFee f.natDegree ell p p+4)) :=
        Finset.sum_le_sum (fun g _=>(group_on_site_exact G D.hf frame i j g (group g)).2)
      _ = _ := by simp [Finset.sum_add_distrib]
  have real := paid_raw_slot_recovers_the_original_completed_product D S pad B R sync reserved frame hv i j raw
  change (paidRawSlot D S pad B R sync reserved frame hv i j raw).steps ≤ head.steps+(∑ g : Fin 64,(group g).run.steps)+
        64*(boxFee f.natDegree ell p p+4)+tupleExtra E.words.length ell p 64+3
  rw [real]
  change head.steps+complete.steps+3 ≤ _
  have h := composed.trans (Nat.add_le_add_right byGroup _)
  omega

def physicalGroupRoof (m n key e install core : ℕ) : ℕ :=
  (ordinalFee 6 63+6*key+17)+(ordinalFee 6 63+8)+
    submittedRowRoof m n key e install+core+10

theorem source_group_roof_at_actual_head
    (i : Centre) (j : Sample) (g : Fin 64) (install core : ℕ)
    (payInstall : ((cachedExteriorJob D S pad (sourceRow (W:=W) D i j g)).install B).steps ≤ install)
    (payCore : (coreRawGroup D S pad B R i j g).steps ≤ core) :
    (paidSourceGroup D S pad B R sync reserved i j g (prepareHead W i j).result rfl).steps ≤ physicalGroupRoof m native (KeyWidth kp tc tj) f.natDegree install core := by
  let head := prepareHead W i j
  let e := emitEntry D.mark (i,j) head.result g
  let ext := entrySource (W:=W) D e.result
  let r := sourceRow (W:=W) D i j g
  let ask := submitResidentRow D S pad B r
  let c := coreRawGroup D S pad B R i j g
  have ord := ordinal_fee_monotone 6 (Nat.le_of_lt_succ g.isLt)
  have E := (actual_entry_wires W D.mark ((i,j),g)).2.2.2.2.2
  change e.steps=ordinalFee 6 g.val+6*KeyWidth kp tc tj+17 at E
  have L := (entry_source_is_actual (W:=W) D r).2.2.2.2
  change ext.steps=ordinalFee 6 g.val+8 at L
  have A : ask.steps ≤ submittedRowRoof m native (KeyWidth kp tc tj) f.natDegree install :=
    true_literal_submit_has_the_local_roof D S pad B i j g install payInstall
  have q := (raw_group_is_the_real_metered_contraction D S pad B R sync reserved i j g head.result rfl).2
  change (paidSourceGroup D S pad B R sync reserved i j g head.result rfl).steps =
    e.steps+ext.steps+ask.steps+c.steps+10 at q
  change c.steps ≤ core at payCore
  rw [q,physicalGroupRoof]
  omega

def physicalSlotRoof (m n tc tj tw kp e p ell install core : ℕ) : ℕ :=
  headRoof m n tc tj tw+
    64*(physicalGroupRoof m n (KeyWidth kp tc tj) e install core+boxFee e ell p p+4)+tupleExtra e ell p 64+3

theorem each_public_slot_has_a_numeric_roof
    (install core : ℕ)
    (payInstall : ∀ (i : Centre) (j : Sample) (g : Fin 64),
      ((cachedExteriorJob D S pad (sourceRow (W:=W) D i j g)).install B).steps ≤ install)
    (payCore : ∀ (i : Centre) (j : Sample) (g : Fin 64), (coreRawGroup D S pad B R i j g).steps ≤ core)
    (i : Centre) (j : Sample) (raw : List Bool) :
    (paidRawSlot D S pad B R sync reserved frame hv i j raw).steps ≤ physicalSlotRoof m native tc tj tw kp f.natDegree (J6SourcePrecision.printed m base) ell install core := by
  let head := prepareHead W i j
  let p := (exteriorChild G ell i j (0:Fin 64)).prec
  let E := SiteFrame G ell frame i
  let bill := ∑ g : Fin 64,(paidSourceGroup D S pad B R sync reserved i j g head.result rfl).steps
  let cap := physicalGroupRoof m native (KeyWidth kp tc tj) f.natDegree install core
  have hHead : head.steps ≤ headRoof m native tc tj tw := by
    have fee := query_head_exact_fee W i j
    change head.steps=_ at fee
    rw [fee,headRoof]
    have t : index m i ≤ 2*m+1 := by
      have h := i.isLt
      unfold index
      omega
    have q := ordinal_fee_monotone tc t
    have jfit := ordinal_fee_monotone tj (Nat.le_of_lt_succ j.isLt)
    omega
  have hBill : bill ≤ 64*cap :=
    (Finset.sum_le_sum (fun g _=>source_group_roof_at_actual_head D S pad B R sync reserved i j g install core
      (payInstall i j g) (payCore i j g))).trans (le_of_eq (by simp [cap]))
  have hP : p=J6SourcePrecision.printed m base := G.precision ell i
  have hF : E.words.length=f.natDegree := E.natDegree D.hf
  have h := printed_outer_slot_has_its_own_group_sum D S pad B R sync reserved frame hv i j raw
  change _ ≤ head.steps+bill+64*(boxFee f.natDegree ell p p+4)+tupleExtra E.words.length ell p 64+3 at h
  rw [hP,hF] at h
  rw [physicalSlotRoof]
  change _ ≤ headRoof m native tc tj tw+
      64*(cap+boxFee f.natDegree ell (J6SourcePrecision.printed m base) (J6SourcePrecision.printed m base)+4)+
      tupleExtra f.natDegree ell (J6SourcePrecision.printed m base) 64+3
  omega

theorem actual_outer_site_rate_from_paid_public_call_cap (Q : ℕ)
    (each : ∀ (i : Centre) (j : Sample),
      (paidRawSlot D S pad B R sync reserved frame hv i j (S.requests.probes.read j).result.val).steps ≤ Q)
    (i : Centre) :
    (rawOuterSite D S pad B R sync reserved frame hv i).steps ≤ rootSiteFee f.natDegree m (literalDegree m native) ell (J6SourcePrecision.printed m base) frame.hp+
        (literalDegree m native+1)*Q := by
  let oracle := outerOracle D S pad B R sync reserved frame hv
  have B0 (j : Sample) : (S.requests.probes.read j).steps ≤ (literalDegree m native+1)*(f.natDegree+2) := by
    rw [resident_probe_input_has_the_original_tariff D S]
    exact ((build_root_probe_receipt G ell).2 j).2
  have siteCap :=
    oracle_site_paid G S.requests.probes B0 oracle hv i
  have direct := each_outer_site_pays_the_actual_public_replies_once D S pad B R sync reserved frame hv i
  have replies : rawOuterSlotBill D S pad B R sync reserved frame hv i ≤ (literalDegree m native+1)*Q := by
    unfold rawOuterSlotBill probeOrder
    rw [List.map_ofFn,List.sum_ofFn]
    exact (Finset.sum_le_sum (fun j _=>each i j)).trans (le_of_eq (by simp))
  rw [direct.fee]
  exact Nat.add_le_add siteCap replies

theorem whole_prescribed_outer_count_has_measured_time
    (Q : ℕ)
    (each : ∀ (i : Centre) (j : Sample),
      (paidRawSlot D S pad B R sync reserved frame hv i j (S.requests.probes.read j).result.val).steps ≤ Q)
    (positiveBase : 0<base) (allZero : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    let out := runRawOuterCount D S pad B R sync reserved frame hv
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    let site := rootSiteFee f.natDegree m (literalDegree m native) ell (J6SourcePrecision.printed m base) frame.hp+
        (literalDegree m native+1)*Q
    bitsValue out.result.val=answer ∧
      out.steps ≤ stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
        legalRootBudget (J6SourcePrecision.printed m base) (printedFactorWidth m n) (printedAnswerWidth m base)
           ell frame.words.length (printedRankWidth m-a m+13*a m) m pads+8+
            gatheredOracleFee m frame.words.length ell (J6SourcePrecision.printed m base) site := by
  have signed := exact_guarded_count_from_the_actual_outer_runs D S pad B R sync reserved frame hv
    positiveBase allZero answer count
  have per := actual_outer_site_rate_from_paid_public_call_cap D S pad B R sync reserved frame hv Q each
  have hg := gather_site_bill frame m _ (rawOuterSite D S pad B R sync reserved frame hv) per
  exact ⟨signed.1,signed.2.trans (Nat.add_le_add_left hg _)⟩

#print axioms printed_outer_slot_has_its_own_group_sum
#print axioms source_group_roof_at_actual_head
#print axioms each_public_slot_has_a_numeric_roof
#print axioms actual_outer_site_rate_from_paid_public_call_cap
#print axioms whole_prescribed_outer_count_has_measured_time
end
end J6R75OuterTime

