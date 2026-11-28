
import J6R30ProducedGateRegistryFrames
import J6R19RetainedBox

/-! One reference bank can hold creation packets of different precisions,
local geometry dimensions, and axis indices for the same source algebra.
A current receiver reads the creation frame, including its old modulus
tape, from the selected reference. Degree compatibility with the new
one follows from the actual shared monic polynomial. -/
namespace J6R30ProducedGateRegistry
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Ancestor J6R20Ancestor J6R19Retained J6R26DescriptorTree

structure FrameShape (f : ℤ[X]) (prec : ℕ) where
  p : ℕ
  a : ℕ
  w : ℕ
  old : List (A1R10.Word p)
  i : Fin a
  birth : J6R15ModeCost.Word prec
  literal : birth.val=p
  pPos : 0<p
  degreePos : 0<old.length
  algebra : Modulus p pPos old=NativeProbeRing.liftPoly p f

structure Envelope (f : ℤ[X]) (ell prec : ℕ) where
  shape : FrameShape f prec
  fields : OriginFields shape.a shape.p ell shape.w shape.old shape.i

abbrev AnyLedger (f : ℤ[X]) (ell key prec tw bw : ℕ) :=
  Ledger key prec tw bw (Envelope f ell prec)

def shapeFrameFee (prec : ℕ) := 3*prec+17

def packCompiled {f : ℤ[X]} {ell prec : ℕ} (S : FrameShape f prec)
    (B : Meter (Option (OriginFields S.a S.p ell S.w S.old S.i))) :
    Meter (Option (Envelope f ell prec)) :=
  let p := duplicateWord S.birth
  let kept : FrameShape f prec := { S with
    birth := p.result
    literal := by
      change (duplicateWord S.birth).result.val=S.p
      rw [duplicate_word_exact]
      exact S.literal }
  ⟨B.result.map (fun v=>⟨kept,v⟩),B.steps+p.steps+13⟩

theorem pack_compiled_exact {f : ℤ[X]} {ell prec : ℕ} (S : FrameShape f prec)
    (B : Meter (Option (OriginFields S.a S.p ell S.w S.old S.i)))
    (F : OriginFields S.a S.p ell S.w S.old S.i) (h : B.result=some F) :
    packCompiled S B=⟨some ⟨S,F⟩,B.steps+shapeFrameFee prec⟩ := by
  have same : (duplicateWord S.birth).result=S.birth := by rw [duplicate_word_exact]
  have paid : (duplicateWord S.birth).steps=3*prec+4 := by rw [duplicate_word_exact]
  have E (x : J6R15ModeCost.Word prec) (hX : x.val=S.p) (e : x=S.birth) :
      (⟨{ S with birth := x, literal := hX },F⟩ : Envelope f ell prec)=⟨S,F⟩ := by
    subst x
    cases S
    rfl
  have unchanged := E (duplicateWord S.birth).result (by rw [same]; exact S.literal) same
  unfold packCompiled
  dsimp only
  rw [h]
  simp only [Option.map_some,unchanged,paid,shapeFrameFee]
  congr 1

def shapeCompatible {f : ℤ[X]} {q prec : ℕ}
    (S : FrameShape f prec) (hf : f.Monic) (hq : 0<q) {new : List (A1R10.Word q)}
    (law : Modulus q hq new=NativeProbeRing.liftPoly q f) :
    S.old.length=new.length :=
  (size_of_monic_words S.pPos hf S.algebra).trans (size_of_monic_words hq hf law).symm

def unwrap {f : ℤ[X]} {ell key prec tw bw : ℕ}
    (r : Stored key prec tw bw (Envelope f ell prec)) :
    Stored key prec tw bw (OriginFields r.payload.shape.a r.payload.shape.p ell
      r.payload.shape.w r.payload.shape.old r.payload.shape.i) :=
  ⟨r.stamp,r.context,r.checkedHeader,r.payload.fields⟩

def consumeEnvelope {f : ℤ[X]} {q ell key prec tw bw : ℕ}
    (hf : f.Monic) (hq : 0<q) (hEll : 0<ell) {new : List (A1R10.Word q)}
    (law : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (addr : J6R15ModeCost.Word key) (depth : ℕ) (wires : List WireRead) (bits : List Bool)
    (B : AnyLedger f ell key prec tw bw) : Meter (Option (UVBlock new ell)) :=
  let z := locate addr B.records
  match z.result with
  | none => ⟨none,z.steps+4⟩
  | some r =>
    let s := r.payload.shape
    let walked := gather (depth+s.a+2) wires bits
    let hD := shapeCompatible s hf hq law
    let out := invokeStored s.pPos s.degreePos hEll hD addr s.birth depth walked.result (unwrap r)
    ⟨out.result,z.steps+walked.steps+out.steps+8⟩

set_option maxHeartbeats 3300000 in
theorem heterogeneous_fetched_packet {f : ℤ[X]} {q ell key prec tw bw : ℕ}
    (hf : f.Monic) (hq : 0<q) (hEll : 0<ell) {new : List (A1R10.Word q)}
    (law : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (addr : J6R15ModeCost.Word key) (depth : ℕ) (wires : List WireRead) (bits : List Bool)
    (B : AnyLedger f ell key prec tw bw) (r : Stored key prec tw bw (Envelope f ell prec))
    (found : (locate addr B.records).result=some r)
    (own : addr=r.stamp.creator) (birth : r.payload.shape.birth=r.stamp.created) :
    let s := r.payload.shape
    let x := r.payload.fields
    let walk := gather (depth+s.a+2) wires bits
    let eval := invokeTrace s.pPos s.degreePos hEll (shapeCompatible s hf hq law)
      x.probe r.context.center s.i r.context.codeWidth.val depth x.rows x.cols x.modes walk.result
    consumeEnvelope hf hq hEll law addr depth wires bits B=
      ⟨some eval.result,(locate addr B.records).steps+walk.steps+eval.steps+invokeStampFee key prec tw bw+8⟩ ∧
      r.stamp.created.val=s.p := by
  let s := r.payload.shape
  let walk := gather (depth+s.a+2) wires bits
  have out := stored_executor_exact s.pPos s.degreePos hEll (shapeCompatible s hf hq law)
    addr s.birth depth walk.result (unwrap r) own birth
  refine ⟨?_,birth ▸ s.literal⟩
  unfold consumeEnvelope
  dsimp only
  rw [found]
  dsimp only
  rw [out]
  dsimp only [unwrap,walk,s]
  congr 1
  omega

#print axioms pack_compiled_exact
#print axioms shapeCompatible
#print axioms heterogeneous_fetched_packet
end J6R30ProducedGateRegistry







