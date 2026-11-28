import J6R53PublicMountReadout

/-! Lower accounting for the complete chosen-root fallback: all
literal centre/probe/group mount transactions are present in its bill. -/
namespace J6R53PublicMount
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R33OriginalJ6 J6R28GeneratedRootFrame
open J6R34OfficialGateway J6R34RootAtlas J6R27OriginalGate J6R14ZeroMode J6R36SharedGateway

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3310
set_option maxHeartbeats 11800000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
variable {ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (hf : f.Monic) (F : Frame f (J6SourcePrecision.printed m base)) (positive : 0<ell)
variable (R : MountedFamily (V:=V) (T:=T) G ell q rr cc dd edgew tc tj key prec tw bw rate pad)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)
variable (i : J6Recovery.Addr m)

theorem mounted_site_pays_every_printed_probe :
    (∑ j : Fin (literalDegree m native+1),∑ g : Fin 64, groupCharge G i j (R i j g)) ≤
      (mountedMeasuredSites G hf F positive R A i).steps := by
  let impl := paidMountedQuery G hf F positive R A
  let O := mountedOracle G hf F positive R
  have delta := actual_paid_site_delta (F:=F) G A impl O
    (fun a b raw legal=>legal_mount_matches_original_oracle G hf F positive R A a b raw legal) positive i
  change _≤(paidSite G A impl hf positive i).steps
  rw [delta.fee]
  refine le_trans ?_ (Nat.le_add_left _ _)
  simp only [probeOrder,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_le_sum
  intro j _
  exact public_legal_reply_pays_every_mount G hf F positive R A i j (A.read j).result.val (A.consistent j)

private theorem counted_site_steps_are_paid
    {p l B W : ℕ} (frame : Frame f p) (hB : 0<B) (hW : 0<W)
    (m l' n' width : ℕ) (cells : J6R14LayoutCost.CellWord)
    (sites : J6Recovery.Addr m→Meter (Block frame l)) :
    ((rowsOfSites frame m sites).map Meter.steps).sum ≤
      (countFromMeasuredSlots frame hB hW m l' n' width cells sites).steps := by
  unfold countFromMeasuredSlots
  dsimp only
  omega

theorem run_mounted_count_pays_every_printed_mount :
    (∑ i : J6Recovery.Addr m,∑ j : Fin (literalDegree m native+1),
       ∑ g : Fin 64,groupCharge G i j (R i j g)) ≤ (runMountedCount G hf F positive R).steps := by
  let bank := buildRootBitBank G ell
  let sites := mountedMeasuredSites G hf F positive R bank.result
  let fits := printed_readout_fits m n base (constantRootWord m)
  let cells := J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (constantRootWord m))
  let finished := countFromMeasuredSlots F fits.1 fits.2.1 m (printedHalf m) n
    (printedRankWidth m) cells sites
  change _≤finished.steps+bank.steps+4
  calc
    _≤∑ i : J6Recovery.Addr m,(sites i).steps :=
      Finset.sum_le_sum (fun i _=>mounted_site_pays_every_printed_probe G hf F positive R bank.result i)
    _=((rowsOfSites F m sites).map Meter.steps).sum := by
      simp only [rowsOfSites,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
    _≤finished.steps := counted_site_steps_are_paid F fits.1 fits.2.1 m (printedHalf m) n
      (printedRankWidth m) cells sites
    _≤_ := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

#print axioms mounted_site_pays_every_printed_probe
#print axioms run_mounted_count_pays_every_printed_mount
end
end J6R53PublicMount
