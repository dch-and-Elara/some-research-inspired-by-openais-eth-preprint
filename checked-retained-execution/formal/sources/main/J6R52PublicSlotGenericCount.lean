import J6R52PublicSlotQuery
import J6R52PublicSlotOrigin

/-! The paid signed decoder for the chosen actual plant, without
coercing new planted ranks to a frozen old archive chart. -/
namespace J6R52PublicSlot
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12 J6R22Active
open J6Mesh J6OrientedHost J6OrientedHostEval J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R33OriginalJ6
open J6R32RootGeneratedRegistryInputs J6R34OfficialGateway J6R36SharedGateway
open J6R25StableCensus J6R22RootReadout J6R28GeneratedRootFrame J6R11Repack
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3350
set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native ell key prec tw bw page speed : ℕ}
variable {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m))
variable (hf : f.Monic) (frame : Frame f (J6SourcePrecision.printed m base)) (hv : 0<ell)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (runs : GroupPrograms (V:=V) (f:=f) (m:=m) (n:=n) (base:=base) (native:=native) (T:=T) G hf ell key prec tw bw page speed)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)

def chosenMeasuredSites (i : J6Recovery.Addr m) : Meter (Block frame ell) :=
  paidSite (F:=frame) G A (paidSlotProgram G hf frame hv runs A) hf hv i

def runChosenCount : Meter (Word (printedAnswerWidth m base)) :=
  let bank := buildRootBitBank G ell
  let sites := chosenMeasuredSites G hf frame hv runs bank.result
  let fits := printed_readout_fits m n base (J6R28GeneratedRootFrame.constantRootWord m)
  let out := countFromMeasuredSlots frame fits.1 fits.2.1 m (printedHalf m) n (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (J6R28GeneratedRootFrame.constantRootWord m))) sites
  ⟨out.result,out.steps+bank.steps+4⟩

theorem measured_site_is_actual_odd_root (i : J6Recovery.Addr m) :
    frame.decode (chosenMeasuredSites G hf frame hv runs A i).result =
      (polynomial
        (stableRootPacking m (printedHalf m) n (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m)
          G.room G.half G.rankA G.rankFit.le)
        (oddAxis m) (index m i:ℤ) (J6SourcePrecision.printed m base) (rootEntryFile f ell base T (J6R28GeneratedRootFrame.constantRootWord m)) hf).eval 0 := by
  let I := paidSlotProgram G hf frame hv runs A
  let O := sourceOracle G hf frame hv runs
  have exactSite := actual_paid_site_delta (F:=frame) G A I O
    (fun a b raw h=>legal_paid_slot_matches_oracle G hf frame hv runs a b A raw h) hv i
  change frame.decode (paidSite (F:=frame) G A I hf hv i).result=_
  rw [exactSite.value]
  exact (oracle_site_exact G A O hv i).1

theorem actual_chosen_public_count (positiveBase : 0<base)
    (allZero : coreA T (fun _=>false)=true) (answer : ℕ)
    (count : Nat.card {x : Fin m→Bool // coreA T x=true ∧ coreB T x=true}=1+answer) :
    let bank := buildRootBitBank G ell
    let sites := chosenMeasuredSites G hf frame hv runs bank.result
    let out := runChosenCount G hf frame hv runs
    let pads := (exactPadOrder m (K m) (printedHalf m) (J6R28GeneratedRootFrame.constantRootWord m)).length
    bitsValue out.result.val=answer ∧
      out.steps≤stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
        legalRootBudget (J6SourcePrecision.printed m base) (printedFactorWidth m n) (printedAnswerWidth m base) ell frame.words.length (printedRankWidth m-a m+13*a m) m pads+
        8+gatherCost frame m sites+bank.steps+4 := by
  let bank := buildRootBitBank G ell
  let sites := chosenMeasuredSites G hf frame hv runs bank.result
  let slots (i : J6Recovery.Addr m) := (slotRead frame m sites i).result
  let fits := printed_readout_fits m n base (J6R28GeneratedRootFrame.constantRootWord m)
  have hF : 0<f.natDegree := frame.natDegree hf ▸ frame.sizePos
  have truth (i : J6Recovery.Addr m) :
      frame.decode (slots i)=
        (polynomial
          (stableRootPacking m (printedHalf m) n (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m)
            G.room G.half G.rankA G.rankFit.le)
          (oddAxis m) (index m i:ℤ) (J6SourcePrecision.printed m base) (rootEntryFile f ell base T (J6R28GeneratedRootFrame.constantRootWord m)) hf).eval 0 := by
    change frame.decode (slotRead frame m sites i).result=_
    rw [(stored_slot_exact frame m sites i).1]
    exact measured_site_is_actual_odd_root G hf frame hv runs bank.result i
  have D := compact_stable_native_words m n base base (printedHalf m) (printedFactorWidth m n) (printedAnswerWidth m base)
    (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m) allZero answer (actual_outer_at_one_guarded_count m n T answer count)
    G.room G.half (printed_rank_width m).1 G.rankA G.rankFit hf positiveBase hF hv
    frame.hp fits.1 fits.2.1 frame.exactMod slots
    (fun i=>by
      have h := truth i
      change boxTransport frame.exactMod (uvRead frame.hp frame.words ell (slots i))=_ at h
      simpa only [boxTransport_cast] using h)
    fits.2.2.1 fits.2.2.2
  have E := metered_slot_append frame fits.1 fits.2.1 m (printedHalf m) n (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (J6R28GeneratedRootFrame.constantRootWord m))) sites
  refine ⟨(congrArg (fun x : Word (printedAnswerWidth m base)=>bitsValue x.val) E.1).trans D.1,?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add_right (E.2.trans (Nat.add_le_add_right D.2 _)) _) _

#print axioms measured_site_is_actual_odd_root
#print axioms actual_chosen_public_count
end
end J6R52PublicSlot
