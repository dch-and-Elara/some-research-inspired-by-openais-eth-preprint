import J6R63ActiveMount
import J6R52CacheWholeBank

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000
set_option maxRecDepth 2700
set_option Elab.async false

/-! The current header is borrowed from the truly successful publisher's
directory head. The result is not rebuilt from the type-level Birth. -/
namespace J6R64Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R63Active J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

def OwnsHeader {key prec tw bw : ℕ} {D : Type*}
    (entry : DirRow key) (B : Ledger key prec tw bw D) : Prop :=
  B.headers.head?=some entry

theorem checked_install_keeps_new_head {key : ℕ} (entry : Meter (DirRow key))
    (old : List (DirRow key)) (success : (checkedInstall entry old).result.2.isSome) :
    (checkedInstall entry old).result.1.head?=some entry.result := by
  unfold checkedInstall at success ⊢
  dsimp only at success ⊢
  cases which : (fetch entry.result.id old).result with
  | some bytes => simp [which] at success
  | none =>
    simp only [copyBytes_exact]
    cases entry.result
    rfl

theorem successful_publish_has_exact_head {key prec tw bw : ℕ} {D : Type*}
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D) (B : Ledger key prec tw bw D)
    (hit : (j.install B).result.2=true) :
    OwnsHeader j.entry.result (j.install B).result.1 := by
  unfold OwnsHeader
  unfold Job.install publishCompiled at hit ⊢
  dsimp only at hit ⊢
  cases has : (checkedInstall j.entry B.headers).result.2 with
  | none => simp [has] at hit
  | some raw =>
    have owned := checked_install_keeps_new_head j.entry B.headers (by rw [has]; rfl)
    simp only [has] at hit ⊢
    cases c : (loadAt prec j.offset raw).result <;>
      cases o : (locate j.entry.result.id B.records).result <;>
      cases d : j.built.result <;>
      simp only [c,o,d,Bool.false_eq_true] at hit
    exact owned

/-- Keep the immutable pointer from the first actual header row. This is
one branch and one field access, not a deep byte-copy. The subsequent
readCallWords still charges its bounded scans and word copies. -/
def borrowHeader {key prec tw bw : ℕ} {D : Type*}
    (B : Ledger key prec tw bw D) : Meter (List Bool) :=
  match B.headers with
  | [] => ⟨[],2⟩
  | head::_ => ⟨head.bytes,3⟩

theorem borrow_exact_live_header {key prec tw bw : ℕ} {D : Type*}
    (entry : DirRow key) (B : Ledger key prec tw bw D) (own : OwnsHeader entry B) :
    borrowHeader B=⟨entry.bytes,3⟩ := by
  unfold OwnsHeader at own
  unfold borrowHeader
  split
  · simp_all
  · rename_i header tail hs
    rw [hs,List.head?_cons,Option.some.injEq] at own
    rw [own]

structure CallWords {f : ℤ[X]} {ell : ℕ} (c : Call (PhysicalHost f ell)) (pw ew : ℕ) where
  precision : Word pw
  edges : Word ew
  precisionValue : precision.val=c.prec
  edgesValue : edges.val=c.edges

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

def readIncoming (X : StoredSite T v key prec tw bw page) (B : PageBank f ell key prec tw bw page)
    (own : OwnsHeader X.birth.job.entry.result B) : Meter (CallWords v.child prec X.birth.edge) :=
  let raw := borrowHeader B
  have auth : raw.result=X.birth.job.entry.result.bytes := by
    have E : raw=⟨X.birth.job.entry.result.bytes,3⟩ := borrow_exact_live_header _ _ own
    rw [E]
  let words := readInherited X.birth raw.result auth
  have exactWords := read_inherited_exact X.birth raw.result auth
  have vals := (actual_birth_header_words X.birth raw.result auth).2
  ⟨⟨words.result.1,words.result.2,
    (congrArg (fun w : Meter (Word prec×Word X.birth.edge)=>w.result.1.val) exactWords).trans vals.1,
    (congrArg (fun w : Meter (Word prec×Word X.birth.edge)=>w.result.2.val) exactWords).trans vals.2⟩,raw.steps+words.steps+2⟩

theorem incoming_words_from_published_head (X : StoredSite T v key prec tw bw page)
    (B : PageBank f ell key prec tw bw page)
    (own : OwnsHeader X.birth.job.entry.result B) :
    let q := readIncoming X B own
    q.result.precision.val=v.child.prec ∧ q.result.edges.val=v.child.edges ∧
      q.steps=callReadFee prec X.birth.edge X.birth.dep X.birth.job.offset+5 := by
  let q := readIncoming X B own
  let raw := borrowHeader B
  have auth : raw.result=X.birth.job.entry.result.bytes := by
    have E : raw=⟨X.birth.job.entry.result.bytes,3⟩ := borrow_exact_live_header _ _ own
    rw [E]
  have p := congrArg Meter.steps (read_inherited_exact X.birth raw.result auth)
  have b : raw.steps=3 := congrArg Meter.steps (borrow_exact_live_header _ _ own)
  refine ⟨q.result.precisionValue,q.result.edgesValue,?_⟩
  change raw.steps+(readInherited X.birth raw.result auth).steps+2=_
  change (readInherited X.birth raw.result auth).steps=callReadFee prec X.birth.edge X.birth.dep X.birth.job.offset at p
  omega

#print axioms successful_publish_has_exact_head
#print axioms borrow_exact_live_header
#print axioms incoming_words_from_published_head
end
end J6R64Active

