import J6R32StatefulArithmeticCore
import J6R30ProducedGateRegistryPhysical
import J6R30ProducedGateRegistryHeterogeneous

/-! Dispatch for original and retained generated gates. The generated
case fetches the envelope from the actual CURRENT bank. A proof-only
homogeneous view of the fetched object is used to apply R30's physical
lemma; no projection bank is built or scanned by the native evaluator. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6ActiveRun J6R10Repack J6R11Blueprint J6R24MeteredRecursion J6R21Ancestor J6R21Leaf
open J6R30ProducedGateRegistry

inductive ReadCode (m key : ℕ) where
  | original (width : ℕ) (tape : OriginalGateTape m width)
  | generated (address : J6R15ModeCost.Word key) (depth : ℕ) (wires : List WireRead)

def ReadCode.run {f : ℤ[X]} {p ell m key prec tw bw : ℕ} (C : ReadCode m key)
    (hf : f.Monic) (F : Frame f p) (hEll : 0<ell) (B : AnyLedger f ell key prec tw bw)
    (bits : List Bool) : Meter (Block F ell) :=
  match C with
  | .original _ tape => uvGate F.hp F.sizePos hEll tape bits
  | .generated id depth wires => requireWord F.hp
    (consumeEnvelope hf F.hp hEll F.exactMod id depth wires bits B)

section Projection
variable {f : ℤ[X]} {p ell key prec tw bw : ℕ}
local notation "L" => AnyLedger f ell key prec tw bw
local notation "W" => (Stored key prec tw bw (J6R30ProducedGateRegistry.Envelope f ell prec))

def homogeneousView (r : W) (addr : J6R15ModeCost.Word key) :
    GateLedger (ell:=ell) (w:=r.payload.shape.w) r.payload.shape.old r.payload.shape.i key prec tw bw :=
  ⟨[],[⟨addr,unwrap r⟩]⟩

theorem view_locates (r : W) (addr : J6R15ModeCost.Word key) :
    locate addr (homogeneousView r addr).records=⟨some (unwrap r),refHeadFee key⟩ :=
  ref_head_exact ⟨addr,unwrap r⟩ []

set_option maxHeartbeats 3000000 in
theorem envelope_word_and_fee (hf : f.Monic) (F : Frame f p) (hEll : 0<ell)
    (B : L) (r : W) (addr : J6R15ModeCost.Word key) (depth : ℕ)
    (wires : List WireRead) (bits : List Bool) (found : (locate addr B.records).result=some r)
    (own : addr=r.stamp.creator) (birth : r.payload.shape.birth=r.stamp.created) :
    let S := r.payload.shape
    let v := gatherAndInvoke S.pPos S.degreePos hEll (shapeCompatible S hf F.hp F.exactMod)
      addr r.stamp.created depth wires bits (homogeneousView r addr)
    let actual := consumeEnvelope hf F.hp hEll F.exactMod addr depth wires bits B
    actual.result=v.result ∧ actual.steps+refHeadFee key=v.steps+(locate addr B.records).steps := by
  let S := r.payload.shape
  let raw := gather (depth+S.a+2) wires bits
  let hD := shapeCompatible S hf F.hp F.exactMod
  have e := (heterogeneous_fetched_packet hf F.hp hEll F.exactMod addr depth wires bits B r found own birth).1
  have hit := fetch_executes_record S.pPos S.degreePos hEll hD addr r.stamp.created depth raw.result
    (homogeneousView r addr) (unwrap r) (congrArg Meter.result (view_locates r addr)) own rfl
  dsimp only
  unfold gatherAndInvoke
  dsimp only
  rw [e,hit,view_locates]
  dsimp only [unwrap,raw,S,hD]
  exact ⟨rfl,by omega⟩
end Projection

section Leaf
variable {f : ℤ[X]} {ell key prec tw bw : ℕ}
structure LeafCode (c : Call (PhysicalHost f ell)) (key : ℕ) where
  sameEdges : c.host.edgeCount=c.edges
  clock : List Unit
  clockShape : clock.length=c.edges
  nodes : List (c.host.Row⊕c.host.Col)
  unique : nodes.Nodup
  complete : ∀ v,v∈nodes
  address : (c.host.Row⊕c.host.Col)→ReadCode c.edges key

variable {c : Call (PhysicalHost f ell)}
def LeafCode.read (D : LeafCode c key) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : AnyLedger f ell key prec tw bw) (v : c.host.Row⊕c.host.Col) (bits : List Bool) :
    Meter (Block F ell) := (D.address v).run hf F hEll B bits

def LeafCode.execute (D : LeafCode c key) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : AnyLedger f ell key prec tw bw) : Meter (Block F ell) :=
  clockDFS F.hp (readProduct F.hp F.sizePos hEll D.nodes (D.read hf F hEll B)) D.clock []

theorem leaf_code_bill (D : LeafCode c key) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : AnyLedger f ell key prec tw bw) :
    let billed := leafEntryBill c.edges D.nodes (D.read hf F hEll B)
    billed≤(D.execute hf F hEll B).steps ∧
    (D.execute hf F hEll B).steps≤billed+
      2^c.edges*(uvWidth F.words.length ell c.prec+D.nodes.length*(mulCap F.words.length ell c.prec+2)+reverseFee c.edges)+
      (2^c.edges-1)*innerFee F.words.length ell c.prec F.hp := by
  dsimp only
  rw [LeafCode.execute,clocked_leaf_is_native_enumerator F.hp F.sizePos hEll D.nodes _ D.clock D.clockShape]
  exact leafCompute_bills_every_entry F.hp F.sizePos hEll c.edges D.nodes (D.read hf F hEll B)

theorem leaf_code_contract (D : LeafCode c key) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : AnyLedger f ell key prec tw bw)
    (entryLaw : ∀ (x : Fin c.edges→Bool) v, F.decode (D.read hf F hEll B v (List.ofFn x)).result=
      (c.host.file v).read hf c.prec (assignment c.host.network (x∘c.host.edgeOrder c.edges D.sameEdges) v)) :
    F.decode (D.execute hf F hEll B).result=J6R9Recursive.reduce c.prec f ell (c.host.contract hf) := by
  rw [LeafCode.execute,clocked_leaf_is_native_enumerator F.hp F.sizePos hEll D.nodes _ D.clock D.clockShape]
  have e (x : Fin c.edges→Bool) (v : c.host.Row⊕c.host.Col) :
    J6R18ChildWrite.castBox F.exactMod (uvRead F.hp F.words ell (D.read hf F hEll B v (List.ofFn x)).result)=
      (c.host.file v).read hf c.prec (assignment c.host.network (x∘c.host.edgeOrder c.edges D.sameEdges) v) :=
    (J6R22Active.boxTransport_cast F.exactMod _).symm.trans (entryLaw x v)
  exact (J6R22Active.boxTransport_cast F.exactMod _).trans
    (actual_leaf_exact c F.hp F.sizePos hEll F.exactMod hf D.sameEdges D.nodes D.unique D.complete _ e)
end Leaf

#print axioms view_locates
#print axioms envelope_word_and_fee
#print axioms leaf_code_bill
#print axioms leaf_code_contract
end J6R32StatefulArithmetic
