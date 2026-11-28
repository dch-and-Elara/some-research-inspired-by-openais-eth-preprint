import J6R35GatewayPreparationShared
import J6R29BinaryFieldSearchRoot

/-! The shared files really can start at R29's made literal selected
field word and R28's made coefficient frame. Those are charged once,
not replaced by a claimed arbitrary Frame meter. -/
namespace J6R35GatewayPreparation
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J7R10Plant J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode
open J6R15ModeCost J6R28GeneratedRootFrame J6R29BinaryFieldSearch
open J6R30GeneratedRootLayout J6R31RootResidentTables
set_option maxHeartbeats 11000000
set_option maxRecDepth 2250
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {base q rr cc dd : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "pm" => J6SourcePrecision.printed
local notation "plant" => physicalPlant (J7R10Readout.H F)

noncomputable def selectedSharedRoot (G : PrintedRootGuard F base)
    (source : LiteralPortFile (physicalPlant (J7R10Readout.H F)) rr cc dd)
    (ell : ℕ) (hq : 0<q) (copies receive : Word q) :
    Meter (ActualRootPreparation (generatedField G).result.rootShape ell q) :=
  let selected := generatedField G
  let S := selected.result
  let root := prepareSharedRoot S.rootShape source ell S.frame hq copies receive
  ⟨root.result,selected.steps+root.steps+4⟩

theorem selected_shared_root_exact (G : PrintedRootGuard F base)
    (source : LiteralPortFile (physicalPlant (J7R10Readout.H F)) rr cc dd)
    (ell : ℕ) (hq : 0<q) (hQ : 1<q) (copies receive : Word q)
    (copyOK : copies.val=K (ms F)) (receiveOK : receive.val=pm (ms F) base) :
    let m := ms F
    let n := literalNativeSize F
    let e := printedFieldWidth m n
    let s := physicalSize m n
    let output := selectedSharedRoot G source ell hq copies receive
    let S := (generatedField G).result
    output.result.frame.words=
      S.lower.val.map (zeroExtend (pm m base)) ∧
    output.steps≤(1024*9^2*2*2^6)*s^8+6+
      (frameBuildFee e (pm m base)+(positiveTapeFee e (literalDegree m n+1)+3)+
        residentsFee m q 0 (pm m base) rr cc dd+storedHalfRowsFee m+6)+4 := by
  let Q := generatedField G
  let S := Q.result
  let m := ms F
  let n := literalNativeSize F
  let A := prepareSharedRoot S.rootShape source ell S.frame hq copies receive
  let e := printedFieldWidth m n
  have frame := S.actual_frame_receipt
  have search := actual_generated_field_polynomial_fee G
  have paid := (actual_shared_paid S.rootShape source ell S.frame hq hQ copies receive copyOK receiveOK).2.1
  refine ⟨frame.1,?_⟩
  change Q.steps+A.steps+4≤_
  change A.steps≤S.frame.steps+(positiveTapeFee S.f.natDegree (literalDegree m n+1)+3)+
    residentsFee m q 0 (pm m base) rr cc dd+storedHalfRowsFee m+6 at paid
  rw [frame.2.2,S.e] at paid
  exact Nat.add_le_add_right (Nat.add_le_add search paid) _

#print axioms selected_shared_root_exact
end J6R35GatewayPreparation
