
import J6R28GeneratedRootFrameLiteral
import J6R27PrescribedProbeCount

/-! Close the remaining caller-supplied root Frame in R27 using the
actual source presentation. The measured evaluation shares one made
coefficient-word tape and one made probe bank. -/
namespace J6R28GeneratedRootFrame
open scoped Polynomial BigOperators Classical
open Polynomial Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J7R10Plant J6R24LegalLayout J6R11Repack
open J6R24MeteredRecursion J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R25StableCensus J6R22RootReadout
set_option maxHeartbeats 13500000
set_option maxRecDepth 2000
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {base : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H
local notation "pm" => J6SourcePrecision.printed

noncomputable def countWithGeneratedFrame (S : FieldInput F base) (ell : ℕ) (hv : 0<ell)
    (children : S.children ell) : Meter (Word (printedAnswerWidth (ms F) base)) :=
  let m := ms F
  let q := qs F
  let w := constantRootWord m
  let widths := printed_readout_fits m q base w
  let made := S.frame
  let count := countFromGeneratedProbes F base (printedHalf m) (literalNativeSize F) (printedRankWidth m)
    (printedFactorWidth m q) (printedAnswerWidth m base) w S.rootShape made.result S.presentation.monic hv
    widths.1 widths.2.1 children
  ⟨count.result,count.steps+made.steps+4⟩

noncomputable def generated_frame_root_fee (S : FieldInput F base) (ell : ℕ) (hv : 0<ell)
    (children : S.children ell) : ℕ :=
  let m := ms F
  let q := qs F
  let native := literalNativeSize F
  let l := printedHalf m
  let width := printedRankWidth m
  let w := constantRootWord m
  let B := printedFactorWidth m q
  let R := printedAnswerWidth m base
  let n := (exactPadOrder m (K m) l w).length
  let d := externalProbeDegree (physicalSize m native)
    (physicalRootCall S.f ell base m l q (physicalPlant (inp F)) w)
  let frame := S.frame.result
  let bank := buildRootBitBank S.rootShape ell
  let I := fun i=>bindLiteralInput (ell:=ell) S.rootShape frame S.presentation.monic i bank.result (children i)
  let sites := fun i=>literalSlot (ell:=ell) S.rootShape frame S.presentation.monic hv i (I i)
  stablePadBudget (a m) (K m) l width+
    legalRootBudget (pm m base) B R ell frame.words.length (width-a m+13*a m) m n+8+
    gatherCost frame m sites+(positiveTapeFee S.f.natDegree (d+1)+3)+4

theorem literal_generated_frame_count (S : FieldInput F base) (ell : ℕ)
    (hv : 0<ell) (children : S.children ell) :
    let R := countWithGeneratedFrame S ell hv children
    bitsValue R.result.val=PinnedCNF.modelCount F ∧
      R.steps≤generated_frame_root_fee S ell hv children+
        frameBuildFee (printedFieldWidth (ms F) (literalNativeSize F)) (pm (ms F) base)+4 := by
  let m := ms F
  let q := qs F
  let w := constantRootWord m
  let widths := printed_readout_fits m q base w
  let Z := S.frame
  letI : Fact (Irreducible (NativeProbeRing.residuePoly S.f)) := ⟨S.irreducible⟩
  have C := generated_prescribed_cnf_count F base (printedHalf m) (literalNativeSize F) (printedRankWidth m)
    (printedFactorWidth m q) (printedAnswerWidth m base) w S.rootShape (printed_rank_width m).1
    Z.result S.presentation.monic S.initialPositive hv widths.1 widths.2.1 children widths.2.2.1 widths.2.2.2
  refine ⟨C.1,?_⟩
  let out := countFromGeneratedProbes F base (printedHalf m) (literalNativeSize F) (printedRankWidth m)
    (printedFactorWidth m q) (printedAnswerWidth m base) w S.rootShape Z.result S.presentation.monic hv
    widths.1 widths.2.1 children
  have H : (Z.steps)=frameBuildFee (printedFieldWidth m (literalNativeSize F)) (pm m base) :=
    S.actual_frame_receipt.2.2
  change out.steps+Z.steps+4≤_
  rw [H]
  exact Nat.add_le_add_right (Nat.add_le_add_right C.2 _) _

#print axioms literal_generated_frame_count
end J6R28GeneratedRootFrame
