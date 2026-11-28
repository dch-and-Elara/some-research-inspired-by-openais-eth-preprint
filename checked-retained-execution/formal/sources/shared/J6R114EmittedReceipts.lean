import J6R114PrescribedReceipts
import J6R75OuterTimeSlotData

/-! The addressed published row is acquired once from the prepared head.
The continuation consumes the actual emitted value, not a free copy of
the canonical proof index. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6Mesh J6OrientedHost J6OrientedHostEval
open J6R24MeteredRecursion J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R28GeneratedRootFrame J6R54PublicFamily J6R57PublicRequest J6R52FreshExterior
open J6R34OfficialGateway J6R36SharedGateway J6R15ModeCost J6R25StableCensus
open J6R33OriginalJ6 J6R22RootReadout J6R11Repack J6R19Retained J6R12Blueprint
open J6R75OuterTime J6R31RootResidentTables J6R14ZeroMode J6R50SourceProducer J1PPrinted
open J6R51Online J6R49Cost J6R10Reachable J6R24LegalLayout

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4900
set_option maxHeartbeats 22000000

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)

abbrev AtWrittenRow :=
  ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (r : Entry D.mark m native tc tj tw),
    r=sourceRow (W:=W) D i j g → r∈S.requests.rows → GroupReceipt (ell:=ell) G D.hf i j g

variable (use : AtWrittenRow D S)

def addressedPaidReceipts : ActualGroupReceipts (W:=W) D :=
  fun i j g head eq =>
    let issued := emitEntry D.mark (i,j) head g
    have index : issued.result=sourceRow (W:=W) D i j g := by subst head; rfl
    have inImage : issued.result∈S.requests.rows :=
      index.symm ▸ canonical_source_row_is_resident D S i j g
    let R := use i j g issued.result index inImage
    ⟨R.frame, ⟨R.run.result,issued.steps+R.run.steps+3⟩, R.truth⟩

theorem each_group_pays_its_emission_and_its_one_continuation
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (head : ExactHead m native tc tj tw i j) (eq : head=(prepareHead W i j).result) :
    let issued := emitEntry D.mark (i,j) head g
    ∃ (index : issued.result=sourceRow (W:=W) D i j g) (inImage : issued.result∈S.requests.rows),
      ((addressedPaidReceipts D S use i j g head eq).run).steps =
        issued.steps+(use i j g issued.result index inImage).run.steps+3 := by
  let issued := emitEntry D.mark (i,j) head g
  have index : issued.result=sourceRow (W:=W) D i j g := by subst head; rfl
  have inImage : issued.result∈S.requests.rows :=
    index.symm ▸ canonical_source_row_is_resident D S i j g
  exact ⟨index,inImage,rfl⟩

#print axioms addressedPaidReceipts
#print axioms each_group_pays_its_emission_and_its_one_continuation
end
end J6R114PrescribedReceipts

