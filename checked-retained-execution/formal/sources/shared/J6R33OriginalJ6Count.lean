import J6R33OriginalJ6Budget
import J6R29BinaryFieldSearchRoot

/-! Oracle-layer J6 on a fixed source-certified chart. Every argument
removed here is an implementation of the oracle, not a promise of
unconditional time for evaluating the slot. -/
namespace J6R33OriginalJ6
open scoped Classical BigOperators Polynomial
open Polynomial Std.Sat A1R10 A1R11 AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J7R10Plant J6R9Recursive J6R11Repack J6R12Repack
open J6R14ZeroMode J6R22Active J6R22RootReadout J6R24LegalLayout J6R24MeteredRecursion
open J6R25StableCensus J6R26StablePreparedRoot J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R29BinaryFieldSearch
set_option maxHeartbeats 18000000
set_option maxRecDepth 2500
set_option exponentiation.threshold 524320
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {ell : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

noncomputable def oracleCount (F : CNF V) (base l native width B R : ℕ)
    (w : Fin (a (ms F))→Fin 64) (G : RootShape f (ms F) l base native width (physicalPlant (inp F)) w)
    (frame : Frame f (pm (ms F) base)) (hf : f.Monic) (hv : 0<ell) (hb : 0<B) (hr : 0<R)
    (O : CompletedOracle G ell frame hf) : Meter (Word R) :=
  let bank := buildRootBitBank G ell
  let sites := fun i=>oracleSite G bank.result O hv i
  let out := countFromMeasuredSlots frame hb hr (ms F) l (qs F) width
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
  ⟨out.result,out.steps+bank.steps+4⟩

def gatheredOracleFee (m e ell p site : ℕ) : ℕ :=
  (m+1)*site+(m+1)^2*(jetEntryWidth e ell p+2)+(m+1)*(jetEntryWidth e ell p+4)+6

theorem gather_site_bill {f : ℤ[X]} {p ell : ℕ} (frame : Frame f p) (m fee : ℕ)
    (sites : J6Recovery.Addr m → Meter (Block frame ell))
    (bound : ∀ i,(sites i).steps≤fee) :
    gatherCost frame m sites≤gatheredOracleFee m frame.words.length ell p fee := by
  have b : ((rowsOfSites frame m sites).map Meter.steps).sum≤(m+1)*fee := by
    rw [rowsOfSites,List.map_ofFn,List.sum_ofFn]
    exact (Finset.sum_le_sum (fun i _=>bound i)).trans (le_of_eq (by simp))
  unfold gatherCost gatheredOracleFee
  omega

def reductionFee (m e native width l B R ell p pads : ℕ) (hp : 0<p) : ℕ :=
  let d := literalDegree m native
  stablePadBudget (a m) (K m) l width+
  legalRootBudget p B R ell e (width-a m+13*a m) m pads+8+
  gatheredOracleFee m e ell p (rootSiteFee e m d ell p hp)+
  (positiveTapeFee e (d+1)+3)+4

theorem supplied_completed_oracle_count [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (F : CNF V) (base l native width B R : ℕ) (w : Fin (a (ms F))→Fin 64)
    (G : RootShape f (ms F) l base native width (physicalPlant (inp F)) w)
    (widthPos : 0<width) (frame : Frame f (pm (ms F) base)) (hf : f.Monic)
    (hbase : 0<base) (hv : 0<ell) (hb : 0<B) (hr : 0<R)
    (O : CompletedOracle G ell frame hf)
    (factorFit : publicFactorWidth (ms F) (qs F) (exactPadOrder (ms F) (K (ms F)) l w).length+2≤B)
    (outerFit : (baseTermWidth (ms F) (outerMeshWidth (ms F)) (pm (ms F) base)+1)*(ms F+1)+3≤R) :
    let m := ms F
    let d := literalDegree m native
    let n := (exactPadOrder m (K m) l w).length
    let out := oracleCount F base l native width B R w G frame hf hv hb hr O
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps≤reductionFee m f.natDegree native width l B R ell (pm m base) n frame.hp ∧
      (requestTrace m d).length=fallbackAddresses m ∧
      (requestTrace m d).length≤(m+1)*(2*(2*(m+2))^(524288+8)+1) := by
  let m := ms F
  let q := qs F
  let n := (exactPadOrder m (K m) l w).length
  let bank := buildRootBitBank G ell
  let d := literalDegree m native
  let e := f.natDegree
  let sites (i : J6Recovery.Addr m) := oracleSite G bank.result O hv i
  let slots (i : J6Recovery.Addr m) := (slotRead frame m sites i).result
  have hF : 0<f.natDegree := frame.natDegree hf ▸ frame.sizePos
  have word (i : J6Recovery.Addr m) :
      frame.decode (slots i)=
        (polynomial (stableRootPacking m l q width (physicalPlant (inp F)) w G.room G.half G.rankA G.rankFit.le)
          (oddAxis m) (index m i:ℤ) (pm m base)
          (rootEntryFile f ell base (physicalPlant (inp F)) w) hf).eval 0 := by
    change frame.decode (slotRead frame m sites i).result=_
    rw [(stored_slot_exact frame m sites i).1]
    exact (oracle_site_exact G bank.result O hv i).1
  have Q := compact_stable_raw_count F base base l B R width w G.room G.half widthPos
    G.rankA G.rankFit hf hbase hF hv frame.hp hb hr frame.exactMod slots
    (fun i=>by
      have h := word i
      change boxTransport frame.exactMod (uvRead frame.hp frame.words ell (slots i))=_ at h
      simpa only [boxTransport_cast] using h) factorFit outerFit
  have A := metered_slot_append frame hb hr m l q width
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
  have P := build_root_probe_receipt G ell
  have bk : bank.steps=positiveTapeFee e (d+1)+3 := P.1
  have per (i : J6Recovery.Addr m) : (sites i).steps≤rootSiteFee e m d ell (pm m base) frame.hp :=
    oracle_site_paid G bank.result (fun j=>(P.2 j).2) O hv i
  have total := gather_site_bill frame m _ sites per
  rw [frame.natDegree hf] at total
  have fee := A.2.trans (Nat.add_le_add_right Q.2 _)
  obtain ⟨qcount,pcount⟩ := request_trace_exact m native G.nativeFits
  refine ⟨(congrArg (fun x : Word R=>bitsValue x.val) A.1).trans Q.1,?_,qcount,pcount⟩
  let raw := countFromMeasuredSlots frame hb hr m l q width
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal w)) sites
  change raw.steps+bank.steps+4≤reductionFee m e native width l B R ell (pm m base) n frame.hp
  change raw.steps≤stablePadBudget (a m) (K m) l width+
    legalRootBudget (pm m base) B R ell frame.words.length (width-a m+13*a m) m n+8+
    gatherCost frame m sites at fee
  rw [frame.natDegree hf] at fee
  unfold reductionFee
  change _≤stablePadBudget (a m) (K m) l width+
    legalRootBudget (pm m base) B R ell e (width-a m+13*a m) m n+8+
    gatheredOracleFee m e ell (pm m base) (rootSiteFee e m d ell (pm m base) frame.hp)+
    (positiveTapeFee e (d+1)+3)+4
  rw [bk]
  exact Nat.add_le_add_right (Nat.add_le_add_right (fee.trans (Nat.add_le_add_left total _)) _) _

#print axioms gather_site_bill
#print axioms supplied_completed_oracle_count
end J6R33OriginalJ6
