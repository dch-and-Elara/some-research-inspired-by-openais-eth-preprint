import J6R32StatefulArithmeticChronology
import J6R30ProducedGateRegistryPackedNative

/-! Typed occurrences retain the entire actual slot path. Reachability
alone is proof-irrelevant and cannot distinguish two occurrence paths
whose semantic Call happens to be equal. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial
open AOracleMachineTime Polynomial J6R21Ancestor J6R24MeteredRecursion
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R30ProducedGateRegistry J6R16ModeCost

variable {f : ℤ[X]} {ell s C key prec tw bw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

inductive Path
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (r : Call (PhysicalHost f ell)) : Call (PhysicalHost f ell)→Type 1 where
  | root : Path sel r r
  | step {c : Call (PhysicalHost f ell)} (path : Path sel r c) (slot : (Plan sel).Slot c) :
      Path sel r ((Plan sel).child c slot)

def Path.reached {c : Call (PhysicalHost f ell)} : Path sel r c→NativeReach (Plan sel) r c
  | .root => .reflexive _
  | .step p w => reach_snoc (Plan sel) p.reached w

def Path.ticket {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c) :
    J6R26DescriptorTree.Ticket sel r := ⟨c,p.reached,w⟩

abbrev GJob (f : ℤ[X]) (ell key prec tw bw : ℕ) :=
  Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (J6R30ProducedGateRegistry.Envelope f ell prec)

structure Birth (T : Prepared cfg sel r hf) (ticket : J6R26DescriptorTree.Ticket sel r)
    (key prec tw bw : ℕ) where
  port : ℕ
  edge : ℕ
  dep : ℕ
  tc : ℕ
  tz : ℕ
  tm : ℕ
  codew : ℕ
  pagew : ℕ
  native : J6R26DescriptorTree.NativeJob T ticket port edge dep prec tc tz tm
  issuance : Meter (J6R15ModeCost.Word key)
  context : CentreContext tw bw
  shape : FrameShape f prec
  actualPrec : shape.p=ticket.child.prec
  frames : Frames shape.old shape.a shape.w codew pagew
  outerPos : 0<ell
  fit : shape.i.val+1≤shape.w
  fields : OriginFields shape.a shape.p ell shape.w shape.old shape.i
  compilerHit : (frames.compile shape.pPos outerPos fit).result=some fields

def Birth.job {T : Prepared cfg sel r hf} {ticket : J6R26DescriptorTree.Ticket sel r}
    (Q : Birth T ticket key prec tw bw) : GJob f ell key prec tw bw :=
  nativePackedJob Q.native Q.issuance Q.context Q.shape Q.actualPrec Q.frames Q.outerPos Q.fit Q.fields Q.compilerHit

theorem issued_prec_and_key {T : Prepared cfg sel r hf} {ticket : J6R26DescriptorTree.Ticket sel r}
    (Q : Birth T ticket key prec tw bw) :
    Q.job.identifier=Q.issuance.result ∧ Q.job.immutable.payload.stamp.created.val=ticket.child.prec := by
  exact ⟨Q.native.job.make_id Q.issuance,Q.shape.literal.trans Q.actualPrec⟩

section Preserve
variable {D : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D

/-- The older source capsule is protected by its immutable matching
header; therefore a legal fresh publisher cannot shadow that creator. -/
def IsLive (j : J) (B : L) : Prop :=
  j.entry.result∈B.headers ∧ (locate j.identifier B.records).result=some j.immutable.payload

theorem live_monotone (j : J) : StableBank (IsLive j) := by
  intro B js hr live
  obtain ⟨row,hit⟩ := live
  constructor
  · rw [(after_jobs_views B js).1]
    exact List.mem_append_right _ row
  · have d : ∀ k∈js,k.identifier≠j.identifier := by
      intro k hk eq
      apply hr.2.2 k hk j.entry.result row
      exact eq.symm
    have different : ∀ x∈(js.map Job.immutable).reverse,x.address≠j.identifier := by
      intro x hx
      rw [List.mem_reverse] at hx
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
      exact d k hk
    rw [(after_jobs_views B js).2,reference_front_fee j.identifier _ _ different]
    exact hit

theorem new_is_live (j : J) (B : L) : IsLive j (afterOne B j) :=
  ⟨List.mem_cons_self,congrArg Meter.result (ref_head_exact j.immutable B.records)⟩
end Preserve

variable {T : Prepared cfg sel r hf}
abbrev Births (T : Prepared cfg sel r hf) (key prec tw bw : ℕ) :=
  ∀ {c : Call (PhysicalHost f ell)} (P : Path sel r c) (w : (Plan sel).Slot c),
    Birth T (P.ticket w) key prec tw bw

variable (births : Births T key prec tw bw)
local notation "L" => AnyLedger f ell key prec tw bw

def Ancestors (rootLive : L→Prop) {c : Call (PhysicalHost f ell)} : Path sel r c→L→Prop
  | .root => rootLive
  | .step path slot => fun B=>Ancestors rootLive path B ∧ IsLive (births path slot).job B

theorem ancestors_stable {rootLive : L→Prop} (stable : StableBank rootLive)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) :
    StableBank (Ancestors births rootLive p) := by
  induction p with
  | root => exact stable
  | step parent w ih =>
    intro B js hr ok
    exact ⟨ih B js hr ok.1,live_monotone (births parent w).job B js hr ok.2⟩

theorem ancestors_enter {rootLive : L→Prop} (stable : StableBank rootLive)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (B : L) (js : List (GJob f ell key prec tw bw))
    (ready : JobsReady B ((births p w).job::js)) (live : Ancestors births rootLive p B) :
    Ancestors births rootLive (.step p w) (afterOne B (births p w).job) := by
  let j := (births p w).job
  have one : JobsReady B [j] := (jobs_split_ready B [j] js ready).1
  exact ⟨ancestors_stable births stable p B [j] one live,new_is_live j B⟩

#print axioms Path.reached
#print axioms issued_prec_and_key
#print axioms live_monotone
#print axioms ancestors_stable
#print axioms ancestors_enter
end J6R32StatefulArithmetic
