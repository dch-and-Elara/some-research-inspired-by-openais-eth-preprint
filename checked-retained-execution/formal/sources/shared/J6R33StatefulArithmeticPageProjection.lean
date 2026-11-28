import J6R33StatefulArithmeticPageCore

/-! Proof projection of a successfully fetched page to the one-capsule
R30 algebra. The actual runtime still does both actual directory scans
and a single Gate invocation. The projected singleton is never run by
the native program. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R21Ancestor J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "L" => PageBank f ell key prec tw bw page
local notation "W" => Stored key prec tw bw (PagedEnvelope f ell prec page)

def projectionBank (r : W) (F : pageFields r) (addr : J6R15ModeCost.Word key) :
    AnyLedger f ell key prec tw bw :=
  ⟨[],[⟨addr,onePage r F⟩]⟩

theorem projection_hit (r : W) (F : pageFields r) (addr : J6R15ModeCost.Word key) :
    locate addr (projectionBank r F addr).records=⟨some (onePage r F),refHeadFee key⟩ :=
  ref_head_exact ⟨addr,onePage r F⟩ []

set_option maxHeartbeats 5500000 in
theorem page_projection_meter {q : ℕ} (hf : f.Monic) (F : Frame f q) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pageWord : J6R15ModeCost.Word page)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool) (B : L)
    (r : W) (above : (locate addr B.records).result=some r)
    (data : pageFields r) (here : (locate pageWord r.payload.pages).result=some data)
    (own : addr=r.stamp.creator) (birth : r.payload.shape.birth=r.stamp.created) :
    let actual := consumePage hf F hEll addr pageWord depth wires bits B
    let fixed := consumeEnvelope hf F.hp hEll F.exactMod addr depth wires bits (projectionBank r data addr)
    ∃ word,actual.result=some word ∧ fixed.result=some word ∧
      actual.steps+refHeadFee key=fixed.steps+(locate addr B.records).steps+
        (locate pageWord r.payload.pages).steps+4 := by
  let fixed := consumeEnvelope hf F.hp hEll F.exactMod addr depth wires bits (projectionBank r data addr)
  let actual := consumePage hf F hEll addr pageWord depth wires bits B
  have cert := consumes_exact_page hf F hEll addr pageWord depth wires bits B r above data here own birth
  have mate := heterogeneous_fetched_packet hf F.hp hEll F.exactMod addr depth wires bits
    (projectionBank r data addr) (onePage r data)
    (congrArg Meter.result (projection_hit r data addr)) own birth
  dsimp only [onePage] at mate
  change ∃ word,actual.result=some word ∧ fixed.result=some word ∧ actual.steps+refHeadFee key=_
  change actual=_ ∧ _ at cert
  change fixed=_ ∧ _ at mate
  refine ⟨_,congrArg Meter.result cert.1,congrArg Meter.result mate.1,?_⟩
  have hA := congrArg Meter.steps cert.1
  have hC := congrArg Meter.steps mate.1
  rw [projection_hit] at hC
  change actual.steps=_ at hA
  change fixed.steps=_ at hC
  change actual.steps+refHeadFee key=fixed.steps+(locate addr B.records).steps+
    (locate pageWord r.payload.pages).steps+4
  rw [hA,hC]
  dsimp only [onePage]
  omega

def readPage {q : ℕ} (hf : f.Monic) (F : Frame f q) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pageWord : J6R15ModeCost.Word page)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool) (B : L) : Meter (Block F ell) :=
  requireWord F.hp (consumePage hf F hEll addr pageWord depth wires bits B)

theorem exact_paged_read_lift {q : ℕ} (hf : f.Monic) (F : Frame f q) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pageWord : J6R15ModeCost.Word page)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool) (B : L)
    (r : W) (above : (locate addr B.records).result=some r)
    (data : pageFields r) (here : (locate pageWord r.payload.pages).result=some data)
    (own : addr=r.stamp.creator) (birth : r.payload.shape.birth=r.stamp.created) :
    let read := readPage hf F hEll addr pageWord depth wires bits B
    let fixed := (ReadCode.generated (m:=bits.length) addr depth wires).run hf F hEll
      (projectionBank r data addr) bits
    read.result=fixed.result ∧ read.steps+refHeadFee key=fixed.steps+(locate addr B.records).steps+
      (locate pageWord r.payload.pages).steps+4 := by
  let A := consumePage hf F hEll addr pageWord depth wires bits B
  let C := consumeEnvelope hf F.hp hEll F.exactMod addr depth wires bits (projectionBank r data addr)
  obtain ⟨y,hA,hC,paid⟩ := page_projection_meter hf F hEll addr pageWord depth wires bits B r above data here own birth
  change (requireWord F.hp A).result=(requireWord F.hp C).result ∧
    (requireWord F.hp A).steps+refHeadFee key=(requireWord F.hp C).steps+(locate addr B.records).steps+
      (locate pageWord r.payload.pages).steps+4
  change A.steps+refHeadFee key=C.steps+(locate addr B.records).steps+
    (locate pageWord r.payload.pages).steps+4 at paid
  rw [requireWord_hit F.hp A y hA,requireWord_hit F.hp C y hC]
  exact ⟨rfl,by change A.steps+2+refHeadFee key=C.steps+2+(locate addr B.records).steps+
                      (locate pageWord r.payload.pages).steps+4; omega⟩

#print axioms projection_hit
#print axioms page_projection_meter
#print axioms exact_paged_read_lift
end J6R33StatefulArithmeticPage
