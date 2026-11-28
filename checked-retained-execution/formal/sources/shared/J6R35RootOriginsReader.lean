import J6R35RootOriginsStable
import J6R33StatefulArithmeticPageBoundRead

/-! Read the very exterior page identified by the origin split using the
existing interpreter. Both lookups, the old creation evaluation, and the
canonical lift are paid. This does not produce the raw wire list. -/
namespace J6R35RootOrigins
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R24MeteredRecursion
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R15ModeCost J6R16ModeCost J6R30ProducedGateRegistry
open J6R18ChildWrite J6R19Retained J6R27OriginalGate J6R22Active J6R9PacketScopes
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 3000

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
local notation "a₀" => (a m)
local notation "p₀" => (J6SourcePrecision.printed m base)
local notation "i₀" => (oddAxis m)
local notation "P₀" => (rootChart T)
local notation "z₀" => (prescribedNode (rootPreset G ell) p₀ ell X.sample)
local notation "t₀" => ((index m X.centre : ℤ))
local notation "rootCall" =>
  (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m))
local notation "oddVal" => (J6RecursiveCrossing.odd_center_valuation m X.centre)

noncomputable def fromExternalValue (k : CanonicalPage m) (z : Residue f ell p₀) : Point f ell := by
  letI := (rootCall).host.finiteEdge
  letI := (rootCall).host.finiteRow
  letI := (rootCall).host.finiteCol
  exact generatedPoint P₀ i₀ (oddVal).1 (oddVal).2.1 z (rootCall).host.file 0 X.group k

private theorem transport_trace_to_read (k : CanonicalPage m) (z : Residue f ell p₀) (hz : z=z₀)
    {cur : Point f ell} (tr : Trace (stableBorn X k) cur) :
    ∃ received : Trace (fromExternalValue X k z) cur,
      received.depth=tr.depth ∧
      ∀ u : PortAt cur,received.literal (originSeed P₀ i₀ X.group k) u =
        tr.literal (originSeed P₀ i₀ X.group k) u := by
  subst z
  exact ⟨tr,rfl,fun _=>rfl⟩

theorem actual_root_row_count_fits (k : CanonicalPage m) :
    (sourceRows P₀ i₀ X.group k (actualWires m)).length<2^q := by
  have R : (sourceRows P₀ i₀ X.group k (actualWires m)).length≤(actualWires m).length := by
    unfold sourceRows scanSubtype
    exact List.length_filterMap_le _ _
  rw [actual_wires_count m] at R
  have e : M m≤p₀ := by
    unfold J6SourcePrecision.printed
    have lo : 8*M m≤(8*M m)*(a m+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  exact (R.trans e).trans_lt (X.precOK ▸ J6R15ModeCost.val_lt X.pre)

theorem true_exterior_seed_entry (pad : ℕ) (k : CanonicalPage m)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (live : IsLive (X.seed pad) B)
    {cur : Point f ell} (tr : Trace (stableBorn X k) cur)
    {current M : ℕ} (F : Frame f current)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ u,u∈ports)
    (wires : List WireRead)
    (wireLaw : wires=ports.map (fun u=>⟨tr.literal (originSeed P₀ i₀ X.group k) u,
      List.replicate (ord.symm (edge u.val)).val true⟩)) :
    let job := X.seed pad
    let page := (widened pad (residentPageKey m k)).result
    let run := readPage X.hf F X.positive job.identifier page tr.depth wires (List.ofFn bits) B
    let N := (writeResidents m X.hq i₀ X.copies X.pre X.source.raw).result.roster.modes.length
    let rs := sourceRows P₀ i₀ X.group k (actualWires m)
    let cs := sourceCols P₀ i₀ X.group k (actualWires m)
    F.decode run.result=(entry cur).read X.hf current
      (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      (entry cur).created=p₀ ∧
      run.steps≤gatherFee (tr.depth+a₀+2) M ports.length+(locate job.identifier B.records).steps+
        (locate page job.immutable.payload.payload.pages).steps+
        invokeFee a₀ X.field.result.words.length ell p₀ current (i₀).val q X.code tr.depth
          ports.length rs.length cs.length N X.field.result.hp+invokeStampFee key prec tw bw+14 := by
  letI := (rootCall).host.finiteEdge
  letI := (rootCall).host.finiteRow
  letI := (rootCall).host.finiteCol
  let j := X.seed pad
  let w := (widened pad (residentPageKey m k)).result
  let r := j.immutable.payload
  let data := X.chosenFields k
  let p := X.field.result.hp
  let ft := X.field.result.exactMod
  let z := castBox ft (uvRead p X.field.result.words ell data.probe)
  have node : z=z₀ := (boxTransport_cast ft _).symm.trans
    ((Classical.choose_spec (stable_exterior_atlas X)).2.2 k)
  obtain ⟨tt,depth,aligned⟩ := transport_trace_to_read X k z node tr
  have raw : wires=ports.map (fun u=>⟨tt.literal (originSeed P₀ i₀ X.group k) u,
      List.replicate (ord.symm (edge u.val)).val true⟩) := by
    refine wireLaw.trans (List.map_congr_left (fun u _=>?_))
    rw [aligned u]
  obtain ⟨hrs,hcs,distinctR,distinctC,allR,allC,ξ,ms,hModes,hMeaning,code⟩ := stable_seed_true_page_law X k
  have Nfit : (writeResidents m X.hq i₀ X.copies X.pre X.source.raw).result.roster.modes.length+1≤2^X.code := by
    rw [Nat.add_comm]
    exact Nat.le_of_lt X.codeValid
  have Rfit := actual_root_row_count_fits X k
  have hit := true_seed_payload_page X pad k
  obtain ⟨value,tag,fee⟩ := true_page_port r X.hf F X.positive P₀ (oddVal).2.2 (oddVal).1
    (oddVal).2.1 (rootCall).host.file X.group k
    (ξ.trans (packet_mode_equiv (P₀).mask i₀ p₀).symm) 0 ms hMeaning
    (sourceRows P₀ i₀ X.group k (actualWires m)) distinctR allR
    (sourceCols P₀ i₀ X.group k (actualWires m)) distinctC allC
    X.code X.hq Nfit Rfit code B j.identifier w live.2 data hit rfl rfl X.signedCentre X.codeTruth
    hrs hcs hModes tt ord bits ports hall wires raw
  rw [depth] at value fee
  exact ⟨value,tag.symm.trans X.birthOK,fee⟩

end J6R35RootOrigins
#print axioms J6R35RootOrigins.actual_root_row_count_fits
#print axioms J6R35RootOrigins.true_exterior_seed_entry
