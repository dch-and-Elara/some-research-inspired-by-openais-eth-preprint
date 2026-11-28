import J6R48LeafRawTape
import J6R33StatefulArithmeticPageLeaf

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10500000
set_option maxRecDepth 2350

/-! Specification-side budget of the actual paged leaf reader. The
runtime performs its existing occurrence scan, page scan, wire reads
and old-precision packet arithmetic exactly once. We price the given
serialized fields, not a supplied entry routine or a uniform fee. -/
namespace J6R48Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R18ChildWrite J6R19Retained J6R20Ancestor J6R21Ancestor J6R21Leaf J6R22Active
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage P1DyadicGrid

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "Bnk" => PageBank f ell key prec tw bw page
local notation "Rec" => Stored key prec tw bw (PagedEnvelope f ell prec page)

/-- These are the source arithmetic/serial format checks for one
existing packet descriptor, not a claim about the value it computes. -/
structure PacketForm (r : Rec) (d : pageFields r) : Prop where
  grid : r.context.center∈P1DyadicGrid.grid r.payload.shape.a
  countWidth : 0<r.payload.shape.w
  codeFit : d.modes.length+1≤2^r.context.codeWidth.val
  rowFit : d.rows.length<2^r.payload.shape.w
  modeCodes : ∀ j : Fin d.modes.length,
    (d.modes.get j).code=encodeBits r.context.codeWidth.val j.succ.val

theorem raw_invoke_fee (r : Rec) (d : pageFields r) (form : PacketForm r d)
    {p : ℕ} (hf : f.Monic) (F : Frame f p) (hEll : 0<ell) (dep : ℕ) (raw : List Raw) :
    let S := r.payload.shape
    (invokeTrace S.pPos S.degreePos hEll (shapeCompatible S hf F.hp F.exactMod)
      d.probe r.context.center S.i r.context.codeWidth.val dep d.rows d.cols d.modes raw).steps ≤
    invokeFee S.a S.old.length ell S.p p S.i.val S.w r.context.codeWidth.val dep
      raw.length d.rows.length d.cols.length d.modes.length S.pPos := by
  let S := r.payload.shape
  let hD := shapeCompatible S hf F.hp F.exactMod
  let t := r.context.center
  let b := r.context.codeWidth.val
  let Q := routeTrace dep d.rows d.cols raw
  let ms : Fin d.modes.length→ModeInput S.a S.p S.i S.w := d.modes.get
  let P := packetResult S.pPos S.degreePos hEll d.probe t S.i b Q.result.1 Q.result.2 d.modes
  have hc (j : Fin d.modes.length) : (ms j).code=encodeBits b j.succ.val := form.modeCodes j
  have hm : List.ofFn ms=d.modes := List.ofFn_get d.modes
  obtain ⟨nr,nc,cost⟩ := raw_route_caps dep d.rows d.cols raw
  change Q.result.1.length=d.rows.length at nr
  change Q.result.2.length=d.cols.length at nc
  have fit : Q.result.1.length<2^S.w := nr ▸ form.rowFit
  have e := (packetResult_exact S.pPos S.degreePos hEll d.probe t form.grid S.i b
    form.countWidth form.codeFit Q.result.1 Q.result.2 fit ms hc).2
  rw [hm,nr,nc] at e
  change P.steps≤_ at e
  have lift := (resizeUV_exact hD P.result).2
  change Q.steps+P.steps+(resizeUV hD P.result).steps+4≤_
  have walk : Q.steps≤traceRouteFee S.a dep raw.length d.rows.length d.cols.length := cost
  unfold invokeFee
  dsimp only [S,b] at e walk lift ⊢
  omega

section Read

/-- Computable, proof-side upper fee derived from the same serialized
lookup that the reader performs. A missing record is priced, not assumed
to have evaluated its target. The correctness theorem uses legal inputs. -/
def rawPageFee (e p m : ℕ) (B : Bnk) (C : PageReadCode m key page) : ℕ :=
  match C with
  | .original w tape=>originalGateFee m w (originalDegree tape)+uvWidth e ell p+4
  | .generated address selector dep wires=>
    let outer := locateFee key B.records.length
    match (locate address B.records).result with
    | none=>outer+uvWidth e ell p+8
    | some r=>
      let inner := locateFee page r.payload.pages.length
      match (locate selector r.payload.pages).result with
      | none=>outer+inner+uvWidth e ell p+12
      | some data=>
        let S := r.payload.shape
        outer+inner+rawWireFee (dep+S.a+2) wires+
          invokeFee S.a S.old.length ell S.p p S.i.val S.w r.context.codeWidth.val dep
            wires.length data.rows.length data.cols.length data.modes.length S.pPos+
          invokeStampFee key prec tw bw+14

def ResidentReadForm {m : ℕ} (B : Bnk) (C : PageReadCode m key page) : Prop :=
  match C with
  | .original _ _=>True
  | .generated a k _ _=>
    ∃ (r : Rec), (locate a B.records).result=some r ∧
      a=r.stamp.creator ∧ r.payload.shape.birth=r.stamp.created ∧
      ∃ (field : pageFields r), (locate k r.payload.pages).result=some field ∧ PacketForm r field

theorem raw_paged_read_bound {p m : ℕ} (hf : f.Monic) (F : Frame f p) (hEll : 0<ell)
    (B : Bnk) (C : PageReadCode m key page) (form : ResidentReadForm B C)
    (bits : List Bool) (size : bits.length=m) :
    (C.run hf F hEll B bits).steps≤rawPageFee F.words.length p m B C := by
  cases C with
  | original w tape =>
    simpa only [PageReadCode.run,rawPageFee,size] using raw_uv_gate_steps F.hp F.sizePos hEll bits tape
  | generated a k dep wires =>
    rcases form with ⟨r,hit,own,birth,data,pageHit,ready⟩
    let S := r.payload.shape
    let walk := gather (dep+S.a+2) wires bits
    let op := invokeTrace S.pPos S.degreePos hEll (shapeCompatible S hf F.hp F.exactMod)
      data.probe r.context.center S.i r.context.codeWidth.val dep data.rows data.cols data.modes walk.result
    have event := (consumes_exact_page hf F hEll a k dep wires bits B r hit data pageHit own birth).1
    have hRun : (readPage hf F hEll a k dep wires bits B).steps =
        (locate a B.records).steps+(locate k r.payload.pages).steps+walk.steps+op.steps+
        invokeStampFee key prec tw bw+14 := by
      unfold readPage
      rw [event,requireWord]
    have boundA := locate_bound a B.records
    have boundK := locate_bound k r.payload.pages
    obtain ⟨walkLen,walkFee⟩ := raw_wire_gather_steps (dep+S.a+2) wires bits
    change walk.result.length=wires.length at walkLen
    change walk.steps≤_ at walkFee
    have hOp := raw_invoke_fee r data ready hf F hEll dep walk.result
    change op.steps≤_ at hOp
    rw [walkLen] at hOp
    change (readPage hf F hEll a k dep wires bits B).steps≤_
    simp only [rawPageFee,hit,pageHit]
    rw [hRun]
    dsimp only [S] at walkFee
    omega
end Read

#print axioms raw_invoke_fee
#print axioms rawPageFee
#print axioms raw_paged_read_bound
end J6R48Leaf
