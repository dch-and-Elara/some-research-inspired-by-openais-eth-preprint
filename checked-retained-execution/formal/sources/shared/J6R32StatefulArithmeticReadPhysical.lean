import J6R32StatefulArithmeticRead
import J6R32StatefulArithmeticPath

/-! Transport R30's actual source-port theorem to the heterogeneous
live registry. In particular the located record, not a substitute with
a different creation precision or output, determines the result. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R21Ancestor J6R20Ancestor J6R18ChildWrite J6R19Retained J6R24MeteredRecursion J6R22Active
open P1DyadicGrid P11FullPacking J6R10Repack J6R11Blueprint J6R9PacketScopes
open J6R30ProducedGateRegistry

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {Net : Network E A B}
variable {f : ℤ[X]} {q ell m M key prec tw bw : ℕ}
variable (r : Stored key prec tw bw (J6R30ProducedGateRegistry.Envelope f ell prec))
local notation "H" => r.payload.shape
local notation "a" => r.payload.shape.a
local notation "p" => r.payload.shape.p
local notation "w" => r.payload.shape.w
local notation "i" => r.payload.shape.i

set_option maxHeartbeats 5300000 in
theorem source_fetched_port
    (hf : f.Monic) (F : Frame f q) (hEll : 0<ell)
    (P : PhysicalPacking Net r.payload.shape.a G) {t : ℤ}
    (ht : t∈grid a) (ht0 : t≠0) (hv : padicValInt 2 t=(i).val)
    (oldFile : EntryFile f ell Net) (g : G) (k : Page a P.copies G)
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ)
    (ms : Fin m→ModeInput a p i w) (hMode : ModeMeaning P i g k ξ β ms)
    (rs : List (RowsOf P i g k)) (hnR : rs.Nodup) (haR : ∀ r',r'∈rs)
    (cs : List (ColsOf P i g k)) (hnC : cs.Nodup) (haC : ∀ c',c'∈cs)
    (b : ℕ) (hw : 0<w) (hb : m+1≤2^b) (hCount : rs.length<2^w)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    (bank : AnyLedger f ell key prec tw bw) (addr : J6R15ModeCost.Word key)
    (found : (locate addr bank.records).result=some r)
    (owner : addr=r.stamp.creator) (birth : r.payload.shape.birth=r.stamp.created)
    (realT : r.context.center=t) (realB : r.context.codeWidth.val=b)
    (hRows : r.payload.fields.rows=rs.map (fun row=>slotWord P row.val))
    (hCols : r.payload.fields.cols=cs.map (fun col=>slotWord P col.val))
    (hModes : r.payload.fields.modes=List.ofFn ms)
    {cur : Point f ell}
    (tr : Trace (generatedPoint P i ht0 hv (castBox r.payload.shape.algebra (uvRead r.payload.shape.pPos r.payload.shape.old ell r.payload.fields.probe))
      oldFile β g k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ v,v∈ports)
    (wires : List WireRead)
    (realWires : wires=ports.map (fun u=>⟨tr.literal (originSeed P i g k) u,
      List.replicate (ord.symm (edge u.val)).val true⟩)) :
    let read := (ReadCode.generated (m:=M) addr tr.depth wires).run hf F hEll bank (List.ofFn bits)
    F.decode read.result=(entry cur).read hf q
      (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      r.stamp.created.val=(entry cur).created ∧
      read.steps≤gatherFee (tr.depth+a+2) M ports.length+(locate addr bank.records).steps+
        invokeFee a r.payload.shape.old.length ell p q (i).val w b tr.depth ports.length rs.length cs.length m r.payload.shape.pPos+
        invokeStampFee key prec tw bw+10 := by
  let homogeneous := homogeneousView r addr
  let actual := consumeEnvelope hf F.hp hEll F.exactMod addr tr.depth wires (List.ofFn bits) bank
  have loc : (locate addr homogeneous.records).result=some (unwrap r) :=
    congrArg Meter.result (view_locates r addr)
  have tag : r.stamp.created.val=p := birth ▸ r.payload.shape.literal
  have heF : 0<f.natDegree := F.natDegree hf ▸ F.sizePos
  obtain ⟨word,hit,val,pinned,fee⟩ := real_lookup_consumes_source hf heF r.payload.shape.pPos F.hp r.payload.shape.algebra
    F.exactMod r.payload.shape.degreePos hEll P i ht ht0 hv oldFile g k ξ β ms hMode rs hnR haR cs hnC haC b
    hw hb hCount hCodes homogeneous addr (unwrap r) loc owner tag realT realB hRows hCols hModes
    tr ord bits ports hall wires realWires
  have meter := envelope_word_and_fee hf F hEll bank r addr tr.depth wires (List.ofFn bits) found owner birth
  have gets : actual.result=some word := meter.1.trans hit
  have read := requireWord_hit F.hp actual word gets
  dsimp only
  change F.decode (requireWord F.hp actual).result=_ ∧ _ ∧ (requireWord F.hp actual).steps≤_
  rw [read]
  refine ⟨(boxTransport_cast F.exactMod _).trans val,pinned,?_⟩
  let z := gatherAndInvoke r.payload.shape.pPos r.payload.shape.degreePos hEll (shapeCompatible H hf F.hp F.exactMod)
      addr r.stamp.created tr.depth wires (List.ofFn bits) homogeneous
  have hMeter : actual.steps+refHeadFee key=z.steps+(locate addr bank.records).steps := meter.2
  change z.steps≤_ at fee
  have count : (locate addr homogeneous.records).steps=refHeadFee key :=
    congrArg Meter.steps (view_locates r addr)
  rw [count] at fee
  change actual.steps+2≤_
  omega

#print axioms source_fetched_port
end J6R32StatefulArithmetic
