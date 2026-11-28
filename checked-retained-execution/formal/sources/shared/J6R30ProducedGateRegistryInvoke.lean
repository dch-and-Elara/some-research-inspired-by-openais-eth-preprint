
import J6R30ProducedGateRegistryLedger
import J6R21AncestorGather

/-! The reply is computed using the actual R21 fetched capsule.
No separate copy of the mathematical payload is passed to the reader.
Both the creator word and its *old* creation precision are checked;
the output precision can differ, and invokeTrace itself performs the
native canonical lift/resize rather than evaluating in the new ring. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime A1R10 J6R21Ancestor J6R20Ancestor

abbrev GateLedger {p a ell w : ℕ} (old : List (A1R10.Word p)) (i : Fin a)
    (key prec tw bw : ℕ) :=
  Ledger key prec tw bw (OriginFields a p ell w old i)

def invokeStampFee (key prec tw bw : ℕ) :=
  (10*key+5)+(10*prec+5)+readContextFee tw bw+9

def invokeStored {p q ell a w key prec tw bw : ℕ} {old : List (A1R10.Word p)}
    {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (addr : J6R15ModeCost.Word key) (want : J6R15ModeCost.Word prec)
    (depth : ℕ) (raw : List Raw)
    (rec : Stored key prec tw bw (OriginFields a p ell w old i)) :
    Meter (Option (UVBlock new ell)) :=
  let author := cmpAddr addr rec.stamp.creator
  let stamp := cmpAddr want rec.stamp.created
  if author.result && stamp.result then
    let site := readContext rec.context
    let b := rec.payload
    let op := invokeTrace hp he hEll hD b.probe site.result.1 i site.result.2 depth
      b.rows b.cols b.modes raw
    ⟨some op.result,author.steps+stamp.steps+site.steps+op.steps+9⟩
  else ⟨none,author.steps+stamp.steps+6⟩

def invokeFromBank {p q ell a w key prec tw bw : ℕ} {old : List (A1R10.Word p)}
    {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (addr : J6R15ModeCost.Word key) (want : J6R15ModeCost.Word prec)
    (depth : ℕ) (raw : List Raw)
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw) :
    Meter (Option (UVBlock new ell)) :=
  let z := locate addr B.records
  match z.result with
  | none => ⟨none,z.steps+4⟩
  | some v =>
    let out := invokeStored hp he hEll hD addr want depth raw v
    ⟨out.result,z.steps+out.steps+4⟩

theorem stored_executor_exact {p q ell a w key prec tw bw : ℕ} {old : List (A1R10.Word p)}
    {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (addr : J6R15ModeCost.Word key) (want : J6R15ModeCost.Word prec) (depth : ℕ) (raw : List Raw)
    (rec : Stored key prec tw bw (OriginFields a p ell w old i))
    (origin : addr=rec.stamp.creator) (tag : want=rec.stamp.created) :
    let v := rec.payload
    let ev := invokeTrace hp he hEll hD v.probe rec.context.center i rec.context.codeWidth.val depth
      v.rows v.cols v.modes raw
    invokeStored hp he hEll hD addr want depth raw rec=
      ⟨some ev.result,ev.steps+invokeStampFee key prec tw bw⟩ := by
  have o := (cmpAddr_exact addr rec.stamp.creator).1.mpr origin
  have p := (cmpAddr_exact want rec.stamp.created).1.mpr tag
  unfold invokeStored invokeStampFee
  dsimp only
  rw [o,p]
  simp only [Bool.and_self,if_true,read_context_exact,(cmpAddr_exact addr rec.stamp.creator).2,
    (cmpAddr_exact want rec.stamp.created).2]
  congr 1
  omega

theorem wrong_creation_guard {p q ell a w key prec tw bw : ℕ} {old : List (A1R10.Word p)}
    {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (addr : J6R15ModeCost.Word key) (want : J6R15ModeCost.Word prec) (depth : ℕ) (raw : List Raw)
    (rec : Stored key prec tw bw (OriginFields a p ell w old i))
    (wrong : want≠rec.stamp.created) :
    (invokeStored hp he hEll hD addr want depth raw rec).result=none := by
  unfold invokeStored
  dsimp only
  have bad : (cmpAddr want rec.stamp.created).result=false := by
    cases e : (cmpAddr want rec.stamp.created).result with
    | false => rfl
    | true => exact (wrong ((cmpAddr_exact _ _).1.mp e)).elim
  rw [bad,Bool.and_false]
  simp only [Bool.false_eq_true,if_false]

theorem fetch_executes_record {p q ell a w key prec tw bw : ℕ} {old : List (A1R10.Word p)}
    {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (addr : J6R15ModeCost.Word key) (want : J6R15ModeCost.Word prec) (depth : ℕ) (raw : List Raw)
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw)
    (rec : Stored key prec tw bw (OriginFields a p ell w old i))
    (located : (locate addr B.records).result=some rec) (origin : addr=rec.stamp.creator)
    (tag : want=rec.stamp.created) :
    let v := rec.payload
    let ev := invokeTrace hp he hEll hD v.probe rec.context.center i rec.context.codeWidth.val depth
      v.rows v.cols v.modes raw
    invokeFromBank hp he hEll hD addr want depth raw B =
      ⟨some ev.result,(locate addr B.records).steps+ev.steps+invokeStampFee key prec tw bw+4⟩ := by
  unfold invokeFromBank
  dsimp only
  rw [located]
  dsimp only
  rw [stored_executor_exact hp he hEll hD addr want depth raw rec origin tag]
  dsimp only
  congr 1
  omega

def gatherAndInvoke {p q ell a w key prec tw bw : ℕ} {old : List (A1R10.Word p)}
    {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (addr : J6R15ModeCost.Word key) (want : J6R15ModeCost.Word prec)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool)
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw) :
    Meter (Option (UVBlock new ell)) :=
  let g := gather (depth+a+2) wires bits
  let z := invokeFromBank hp he hEll hD addr want depth g.result B
  ⟨z.result,g.steps+z.steps+4⟩

#print axioms stored_executor_exact
#print axioms wrong_creation_guard
#print axioms fetch_executes_record
end J6R30ProducedGateRegistry




