import J6R33OriginalJ6Count

/-! Compose the exact completed oracle reduction with the actual
deterministic field search of the original compiled branch. -/
namespace J6R33OriginalJ6
open scoped Polynomial Classical
open Polynomial Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J7R10Plant J6R11Repack J6R14ZeroMode
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R29BinaryFieldSearch
set_option maxHeartbeats 1600000
set_option maxRecDepth 2200
set_option exponentiation.threshold 524320
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {base : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "pm" => J6SourcePrecision.printed

noncomputable abbrev LiteralCallback (G : PrintedRootGuard F base) (ell : ℕ) :=
  let S := (generatedField G).result
  CompletedOracle S.rootShape ell S.frame.result S.presentation.monic

noncomputable def literalOfficialRun (G : PrintedRootGuard F base) (ell : ℕ) (hv : 0<ell)
    (O : LiteralCallback G ell) : Meter (Word (printedAnswerWidth (ms F) base)) :=
  let A := generatedField G
  let S := A.result
  let E := S.frame
  let m := ms F
  let q := qs F
  let w := constantRootWord m
  let widths := printed_readout_fits m q base w
  let out := oracleCount F base (printedHalf m) (literalNativeSize F) (printedRankWidth m)
    (printedFactorWidth m q) (printedAnswerWidth m base) w S.rootShape E.result
    S.presentation.monic hv widths.1 widths.2.1 O
  ⟨out.result,A.steps+E.steps+out.steps+4⟩

theorem literal_original_J6 (G : PrintedRootGuard F base) (ell : ℕ) (hv : 0<ell)
    (O : LiteralCallback G ell) :
    let m := ms F
    let q := qs F
    let n := literalNativeSize F
    let w := constantRootWord m
    let l := printedHalf m
    let width := printedRankWidth m
    let B := printedFactorWidth m q
    let R := printedAnswerWidth m base
    let A := generatedField G
    let S := A.result
    let out := literalOfficialRun G ell hv O
    bitsValue out.result.val = PinnedCNF.modelCount F ∧
    out.steps = A.steps + S.frame.steps +
      (oracleCount F base l n width B R w S.rootShape S.frame.result
        S.presentation.monic hv (printed_readout_fits m q base w).1
        (printed_readout_fits m q base w).2.1 O).steps+4 ∧
    (requestTrace m (literalDegree m n)).length = (m+1)*(M m*(2*L m-1)+1) ∧
    (requestTrace m (literalDegree m n)).length ≤ (m+1)*(2*(2*(m+2))^(524288+8)+1) := by
  let A := generatedField G
  let S := A.result
  let E := S.frame
  let m := ms F
  let q := qs F
  let n := literalNativeSize F
  let l := printedHalf m
  let width := printedRankWidth m
  let B := printedFactorWidth m q
  let R := printedAnswerWidth m base
  let W := constantRootWord m
  let widths := printed_readout_fits m q base W
  letI : Fact (Irreducible (NativeProbeRing.residuePoly S.f)) := ⟨S.irreducible⟩
  have Q := supplied_completed_oracle_count (f:=S.f) (ell:=ell) F base l n width B R W S.rootShape
    (printed_rank_width m).1 E.result S.presentation.monic S.initialPositive hv
    widths.1 widths.2.1 O widths.2.2.1 widths.2.2.2
  exact ⟨Q.1,rfl,Q.2.2.1,Q.2.2.2⟩

#print axioms literal_original_J6
end J6R33OriginalJ6
