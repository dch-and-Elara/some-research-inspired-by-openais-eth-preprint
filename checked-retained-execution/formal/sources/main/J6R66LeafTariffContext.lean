import J6R66LeafTariffExterior
import J6R66LeafTariffRegistry

/-! The generic stable exterior admits overserialized context words.
This is a counterexample to a source-size-only bound without a
normal-setting condition, even on the actual mounted exterior reader.
The packet and signed centre do not change. -/
namespace J6R66LeafTariff
open scoped Polynomial Classical
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R20Ancestor J6R19Retained
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R26StablePreparedRoot
open J6R34RootAtlas J6R31RootResidentTables J6R35RootOrigins J6R24MeteredRecursion

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 19000000
set_option maxRecDepth 3500

private theorem encode_at_wider_capacity {b : ℕ} (q : Word b) (k : ℕ) :
    (word (q:=b+k) q.val).val=q.val :=
  word_val ((val_lt q).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right b k)))

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}

def widerExterior (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw) (extra : ℕ) :
    StableExterior G ell q ro co d edgew tc tj key prec tw (bw+extra) where
  positive := X.positive
  field := X.field
  hf := X.hf
  source := X.source
  centre := X.centre
  sample := X.sample
  group := X.group
  address := X.address
  timeOK := X.timeOK
  sampleOK := X.sampleOK
  groupOK := X.groupOK
  edgePos := X.edgePos
  edgeFit := X.edgeFit
  issue := X.issue
  birth := X.birth
  birthOK := X.birthOK
  hq := X.hq
  qFits := X.qFits
  copies := X.copies
  pre := X.pre
  copiesOK := X.copiesOK
  precOK := X.precOK
  copyFits := X.copyFits
  code := X.code
  codePos := X.codePos
  codeValid := X.codeValid
  context := ⟨X.context.negative,X.context.magnitude,word (q:=bw+extra) X.context.codeWidth.val⟩
  signedCentre := X.signedCentre
  codeTruth := (encode_at_wider_capacity X.context.codeWidth extra).trans X.codeTruth

theorem exterior_successful_read_bills_context_width
    (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
    (pad : ℕ) (k : CanonicalPage m)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (live : IsLive (X.seed pad) B)
    {p : ℕ} (F : Frame f p) (depth : ℕ) (wires : List WireRead) (bits : List Bool) :
    bw≤(readPage X.hf F X.positive (X.seed pad).identifier
      (widened pad (residentPageKey m k)).result depth wires bits B).steps := by
  let job := X.seed pad
  let recd := job.immutable.payload
  let fld : pageFields recd := X.chosenFields k
  let word := (widened pad (residentPageKey m k)).result
  let S := recd.payload.shape
  let walk := gather (depth+S.a+2) wires bits
  let op := invokeTrace S.pPos S.degreePos X.positive (shapeCompatible S X.hf F.hp F.exactMod)
    fld.probe recd.context.center S.i recd.context.codeWidth.val depth
    fld.rows fld.cols fld.modes walk.result
  have exactRun := (consumes_exact_page X.hf F X.positive job.identifier word depth wires bits B
    recd live.2 fld (true_seed_payload_page X pad k) rfl rfl).1
  have fee : (readPage X.hf F X.positive job.identifier word depth wires bits B).steps =
    (locate job.identifier B.records).steps+(locate word recd.payload.pages).steps+walk.steps+
      op.steps+invokeStampFee key prec tw bw+14 := by
    unfold readPage
    rw [exactRun,requireWord]
  change bw≤(readPage X.hf F X.positive job.identifier word depth wires bits B).steps
  rw [fee]
  have b : bw≤bw*(8*bw+10) := Nat.le_mul_of_pos_right _ (by omega)
  unfold invokeStampFee readContextFee
  omega

/-- The very same logical input, field, precision, physical atlas and
external ordinal can use an arbitrarily wide internal context word.
The bound is on an actual successful native read from an empty mount,
not an upper tariff for a failed or hypothetical lookup. -/
theorem unchanged_atlas_is_not_a_context_fee_cap
    (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
    (extra pad : ℕ) (k : CanonicalPage m) {p : ℕ} (F : Frame f p)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool) :
    let W := widerExterior X extra
    let B := (mountFromEmpty (W.seed pad)).result.1
    W.atlas=X.atlas ∧ W.context.center=X.context.center ∧ W.context.codeWidth.val=X.context.codeWidth.val ∧
    extra≤(readPage W.hf F W.positive (W.seed pad).identifier
      (widened pad (residentPageKey m k)).result depth wires bits B).steps := by
  let W := widerExterior X extra
  refine ⟨rfl,rfl,encode_at_wider_capacity X.context.codeWidth extra,?_⟩
  exact (Nat.le_add_left extra bw).trans
    (exterior_successful_read_bills_context_width W pad k _ (actual_empty_mount (W.seed pad)).2.1
      F depth wires bits)

#print axioms widerExterior
#print axioms exterior_successful_read_bills_context_width
#print axioms unchanged_atlas_is_not_a_context_fee_cap
end J6R66LeafTariff
