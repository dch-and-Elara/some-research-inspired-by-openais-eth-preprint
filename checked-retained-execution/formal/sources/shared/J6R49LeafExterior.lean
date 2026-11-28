import J6R49LeafOriginal
import J6R48LeafBirthFormat
import J6R35RootOriginsReader

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 19500000
set_option maxRecDepth 3300

/-! Exterior original zero-mode page rows, on their actual born page
of the one fixed exterior seed. Both reads are the same native readers
as R35; there is no leaf output callback. -/
namespace J6R49Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R24MeteredRecursion
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R15ModeCost J6R16ModeCost
open J6R30ProducedGateRegistry J6R18ChildWrite J6R19Retained J6R27OriginalGate
open J6R22Active J6R9PacketScopes J6R35RootOrigins J6R48Leaf

noncomputable section
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

theorem exterior_actual_page_format (pad : ℕ) (k : CanonicalPage m)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (alive : IsLive (X.seed pad) B)
    {N : ℕ} (dep : ℕ) (wires : List WireRead) :
    ResidentReadForm B (PageReadCode.generated (edges:=N) (X.seed pad).identifier
      (widened pad (residentPageKey m k)).result dep wires) := by
  let job := X.seed pad
  let record := job.immutable.payload
  let data : pageFields record := X.chosenFields k
  have hit : (locate (widened pad (residentPageKey m k)).result record.payload.pages).result=some data :=
    true_seed_payload_page X pad k
  obtain ⟨hrs,_,_,_,_,_,_,ms,hModes,_,hCodes⟩ := stable_seed_true_page_law X k
  refine ⟨record,alive.2,rfl,rfl,data,hit,?_⟩
  refine ⟨?_,X.hq,?_,?_,?_⟩
  · change X.context.center∈P1DyadicGrid.grid a₀
    rw [X.signedCentre]
    exact (J6RecursiveCrossing.odd_center_valuation m X.centre).2.2
  · change (X.chosenFields k).modes.length+1≤2^X.context.codeWidth.val
    rw [hModes,List.length_ofFn,X.codeTruth,Nat.add_comm]
    exact Nat.le_of_lt X.codeValid
  · change (X.chosenFields k).rows.length<2^q
    rw [hrs,List.length_map]
    exact actual_root_row_count_fits X k
  · change ∀ j : Fin (X.chosenFields k).modes.length,
      ((X.chosenFields k).modes.get j).code=encodeBits X.context.codeWidth.val j.succ.val
    rw [X.codeTruth]
    exact list_modes_have_source_codes ms X.code hCodes _ hModes

variable {c : Call (PhysicalHost f ell)} (F : Frame f c.prec) (pos : 0<ell)
variable (ord : Fin c.edges≃c.host.Edge) (vertex : Vertex c)

def exteriorRow (pad : ℕ) (k : CanonicalPage m)
    (live : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (admitted : ∀ B,live B→IsLive (X.seed pad) B)
    (tr : Trace (stableBorn X k) (atVertex c vertex)) :
    RowAt X.hf F pos ord vertex live where
  code := PageReadCode.generated (X.seed pad).identifier (widened pad (residentPageKey m k)).result
    tr.depth (literalWires vertex tr (originSeed P₀ i₀ X.group k) ord)
  value B good bits := (true_exterior_seed_entry X pad k B (admitted B good) tr F ord bits
    (portList vertex) (portList_complete vertex) _ rfl).1
  format B good := exterior_actual_page_format X pad k B (admitted B good) _ _

#print axioms exterior_actual_page_format
#print axioms exteriorRow
end
end J6R49Leaf
