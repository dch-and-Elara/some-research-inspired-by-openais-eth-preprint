import J6R33StatefulArithmeticPageJob
import J6R32StatefulArithmeticChronActive
import J6R32StatefulArithmeticPath

namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Ancestor J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R30ProducedGateRegistry J6R26DescriptorTree J6R32StatefulArithmetic

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}

structure Birth (T : Prepared cfg sel r hf) (ticket : Ticket sel r) (key prec tw bw page : ℕ) where
  port : ℕ
  edge : ℕ
  dep : ℕ
  tc : ℕ
  tz : ℕ
  tm : ℕ
  native : NativeJob T ticket port edge dep prec tc tz tm
  issuance : Meter (J6R15ModeCost.Word key)
  ctx : CentreContext tw bw
  shape : FrameShape f prec
  actualPrec : shape.p=ticket.child.prec
  compilePages : Meter (Option (PageRows shape ell page))
  rows : PageRows shape ell page
  success : compilePages.result=some rows
  keysUnique : (rows.map RefRow.address).Nodup

def Birth.job {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
    (Q : J6R33StatefulArithmeticPage.Birth T ticket key prec tw bw page) :
    PageJob f ell key prec tw bw page :=
  pagedJob Q.native Q.issuance Q.ctx Q.shape Q.actualPrec Q.compilePages Q.rows Q.success

theorem Birth.tag {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
    (Q : J6R33StatefulArithmeticPage.Birth T ticket key prec tw bw page) :
    Q.job.identifier=Q.issuance.result ∧ Q.job.immutable.payload.stamp.created.val=ticket.child.prec :=
  ⟨Q.native.job.make_id _,Q.shape.literal.trans Q.actualPrec⟩

abbrev Births (T : Prepared cfg sel r hf) (key prec tw bw page : ℕ) :=
  ∀ {c : Call (PhysicalHost f ell)} (P : Path sel r c) (w : (Plan sel).Slot c),
    J6R33StatefulArithmeticPage.Birth T (P.ticket w) key prec tw bw page

variable {T : Prepared cfg sel r hf} (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
local notation "L" => PageBank f ell key prec tw bw page

def opened (rootLive : L→Prop) {c : Call (PhysicalHost f ell)} : Path sel r c→L→Prop
  | .root => rootLive
  | .step p w => fun B=>opened rootLive p B ∧ IsLive (born p w).job B

theorem opened_stable {rootLive : PageBank f ell key prec tw bw page→Prop} (stable : StableBank rootLive)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) :
    StableBank (opened born rootLive p) := by
  induction p with
  | root => exact stable
  | step parent w ih =>
    intro B js ready ok
    exact ⟨ih B js ready ok.1,live_monotone (born parent w).job B js ready ok.2⟩

theorem enter_opened {rootLive : PageBank f ell key prec tw bw page→Prop} (stable : StableBank rootLive)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (B : L) (js : List (PageJob f ell key prec tw bw page))
    (ok : JobsReady B ((born p w).job::js)) (live : opened born rootLive p B) :
    opened born rootLive (.step p w) (afterOne B (born p w).job) := by
  let j := (born p w).job
  have hOne : JobsReady B [j] := (jobs_split_ready B [j] js ok).1
  exact ⟨opened_stable born stable p B [j] hOne live,new_is_live j B⟩

/-- The actual selected creator is in the ancestry, not guessed from
equal call values, equal page values, or a shared birth precision. -/
inductive OnPath (j : PageJob f ell key prec tw bw page) :
    ∀ {c : Call (PhysicalHost f ell)},Path sel r c→Prop where
  | youngest {c} (p : Path sel r c) (w : (Plan sel).Slot c) (eq : (born p w).job=j) :
      OnPath j (.step p w)
  | inherited {c} (p : Path sel r c) (w : (Plan sel).Slot c) (was : OnPath j p) :
      OnPath j (.step p w)

theorem ancestor_paged_live (j : PageJob f ell key prec tw bw page)
    {rootLive : PageBank f ell key prec tw bw page→Prop}
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (origin : OnPath born j p)
    (B : L) (current : opened born rootLive p B) : IsLive j B := by
  induction origin with
  | youngest p w eq =>
    change opened born rootLive p B ∧ IsLive (born p w).job B at current
    exact eq ▸ current.2
  | inherited p w was ih =>
    change opened born rootLive p B ∧ IsLive (born p w).job B at current
    exact ih current.1

#print axioms Birth.tag
#print axioms opened_stable
#print axioms enter_opened
#print axioms ancestor_paged_live
end J6R33StatefulArithmeticPage
