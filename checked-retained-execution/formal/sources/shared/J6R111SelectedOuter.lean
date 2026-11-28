import J6R111SelectedSlot
import J6R75OuterTimeCount

/-! Use the newly paid point values in the original interpolation,
signed readout and count. The comparison run supplies only a proof
of equivalence; it is not executed by the selected program. -/
namespace J6R111SelectedGroup
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R34ChildPath J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R52FreshExterior J6R57PublicRequest J6R54PublicFamily
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R28GeneratedRootFrame J6R14ZeroMode J6R34OfficialGateway A1R12 A1R10
open J6R68ActiveInputs.Sweep J6R75OuterTime J6R19Retained J1PPrinted
open J6R36SharedGateway J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout

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
open J6R26DescriptorTree
open J6R30ProducedGateRegistry
open J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs
open J6R35GatewayPreparation
open J6R35RootOrigins
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
set_option maxRecDepth 5000
set_option maxHeartbeats 24000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

private theorem sum_replace_by_plus {A : Type*} (xs : List A) (new old fee : A→ℕ)
    (law : ∀ a,new a=old a+fee a) :
    (xs.map new).sum=(xs.map old).sum+(xs.map fee).sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons,law a,ih]
    omega

/-- The exact data retained by the final readout are the site
results, whereas its first-phase bill uses every newly charged run. -/
theorem identical_collected_sites_pass_their_exact_new_debits
    {f : ℤ[X]} {p ell B R : ℕ} (F : Frame f p) (hb : 0<B) (hr : 0<R)
    (m l q width : ℕ) (cells : J6R14LayoutCost.CellWord)
    (new old : J6Recovery.Addr m→Meter (Block F ell)) (fee : J6Recovery.Addr m→ℕ)
    (eq : ∀ i,Delta (new i) (old i) (fee i)) :
    Delta (countFromMeasuredSlots F hb hr m l q width cells new)
      (countFromMeasuredSlots F hb hr m l q width cells old)
      (List.ofFn fee).sum := by
  have v : (rowsOfSites F m new).map Meter.result=(rowsOfSites F m old).map Meter.result := by
    simp only [rowsOfSites,List.map_ofFn]
    congr 1
    funext i
    exact (eq i).value
  have k0 : (rowsOfSites F m new).map Meter.steps=List.ofFn (fun i=>(new i).steps) := by
    simp only [rowsOfSites,List.map_ofFn,Function.comp_def]
  have k1 : (rowsOfSites F m old).map Meter.steps=List.ofFn (fun i=>(old i).steps) := by
    simp only [rowsOfSites,List.map_ofFn,Function.comp_def]
  have paid : ((rowsOfSites F m new).map Meter.steps).sum=
      ((rowsOfSites F m old).map Meter.steps).sum+(List.ofFn fee).sum := by
    rw [k0,k1,List.sum_ofFn,List.sum_ofFn,List.sum_ofFn,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _=>(eq i).fee)
  unfold countFromMeasuredSlots
  dsimp only
  rw [v,paid]
  exact ⟨rfl,by dsimp only; omega⟩

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
variable (frame : Frame f (J6SourcePrecision.printed m base)) (hv : 0<ell)

def newOuterSite (i : (J6Recovery.Addr m)) : Meter (Block frame ell) :=
  paidSite G S.requests.probes (paidSelectedSlot D S pad prior R sync reserved setups frame hv)
    D.hf hv i

def oneSiteSelectedExtra (i : (J6Recovery.Addr m)) : ℕ :=
  ((probeOrder (literalDegree m native+1)).map (fun j=>
    ∑ g : Fin 64, selectedGroupExtra D S pad prior R sync reserved setups i j g)).sum

theorem each_real_site_folds_its_actual_selected_slots (i : (J6Recovery.Addr m)) :
    Delta (newOuterSite D S pad prior R sync reserved setups frame hv i)
      (rawOuterSite D S pad prior R sync reserved frame hv i)
      (oneSiteSelectedExtra D S pad prior R sync reserved setups i) := by
  let N := paidSelectedSlot D S pad prior R sync reserved setups frame hv
  let O := paidRawSlot D S pad prior R sync reserved frame hv
  let source := outerOracle D S pad prior R sync reserved frame hv
  have good (i : (J6Recovery.Addr m)) (j : (Fin (literalDegree m native+1))) (b : List Bool)
      (legal : b=List.ofFn ((rootPreset G ell).word j)) :
      (N i j b).result=source.reply i j b :=
    (actual_selected_slot_charges_its_64_real_setups D S pad prior R sync reserved setups
      frame hv i j b).value.trans
       (paid_raw_legal_slot_has_the_same_value D S pad prior R sync reserved frame hv i j b legal)
  have d0 := actual_paid_site_delta G S.requests.probes N source good hv i
  have d1 := each_outer_site_pays_the_actual_public_replies_once D S pad prior R sync reserved frame hv i
  let list := probeOrder (literalDegree m native+1)
  let a := fun j=>(N i j (S.requests.probes.read j).result.val).steps
  let b := fun j=>(O i j (S.requests.probes.read j).result.val).steps
  let fee := fun j=>∑ g : Fin 64,selectedGroupExtra D S pad prior R sync reserved setups i j g
  have qa (j : (Fin (literalDegree m native+1))) : a j=b j+fee j :=
    (actual_selected_slot_charges_its_64_real_setups D S pad prior R sync reserved setups
      frame hv i j (S.requests.probes.read j).result.val).fee
  have h := sum_replace_by_plus list a b fee qa
  have nCost : (newOuterSite D S pad prior R sync reserved setups frame hv i).steps=
      (oracleSite G S.requests.probes source hv i).steps+(list.map a).sum := d0.fee
  have oCost : (rawOuterSite D S pad prior R sync reserved frame hv i).steps=
      (oracleSite G S.requests.probes source hv i).steps+(list.map b).sum := d1.fee
  exact ⟨d0.value.trans d1.value.symm, by
    change _=_+(list.map fee).sum
    omega⟩

def runChosenOuterCount : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  let fit := printed_readout_fits m n base (constantRootWord m)
  countFromMeasuredSlots frame fit.1 fit.2.1 m (printedHalf m) n (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (constantRootWord m)))
    (newOuterSite D S pad prior R sync reserved setups frame hv)

theorem chosen_outer_count_includes_every_actual_setup :
    Delta (runChosenOuterCount D S pad prior R sync reserved setups frame hv)
      (runRawOuterCount D S pad prior R sync reserved frame hv)
      (List.ofFn (oneSiteSelectedExtra D S pad prior R sync reserved setups)).sum := by
  let fit := printed_readout_fits m n base (constantRootWord m)
  exact identical_collected_sites_pass_their_exact_new_debits frame fit.1 fit.2.1 m (printedHalf m) n
    (printedRankWidth m) _ _ _ _ (each_real_site_folds_its_actual_selected_slots
      D S pad prior R sync reserved setups frame hv)

#print axioms identical_collected_sites_pass_their_exact_new_debits
#print axioms each_real_site_folds_its_actual_selected_slots
#print axioms chosen_outer_count_includes_every_actual_setup
end
end J6R111SelectedGroup
