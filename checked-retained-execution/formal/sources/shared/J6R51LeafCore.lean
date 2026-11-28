import J6R50LeafStreaming
import J6R50SourceProducerOnline

/-! The leaf decision is made from the actual born site, not a
separately supplied path-to-patch function. The selected physical
edge book is acquired once and its list spine decides which branch
is taken. For a genuine zero-edge child no read program is attempted. -/
namespace J6R51Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime J6R50Leaf J6R15ModeCost
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R22Active J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R49DFS J6R50SourceProducer
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18500000
set_option maxRecDepth 3200

def dispatchBook {A : Type} {w : ℕ}
    (book : Meter (List (Word w))) (old : Unit→Meter A)
    (acquire : Meter (List (Word w))→Meter (Option A)) : Meter A :=
  match book.result with
  | [] =>
    let r := old ()
    ⟨r.result,book.steps+r.steps+3⟩
  | _::_ =>
    let r := attemptedOr (acquire book) old
    ⟨r.result,r.steps+3⟩

theorem empty_book_preserves_leaf {A : Type} {w : ℕ}
    (book : Meter (List (Word w))) (old : Unit→Meter A)
    (acquire : Meter (List (Word w))→Meter (Option A))
    (empty : book.result=[]) :
    dispatchBook book old acquire=⟨(old ()).result,book.steps+(old ()).steps+3⟩ := by
  unfold dispatchBook
  rw [empty]

theorem nonempty_book_success {A : Type} {w : ℕ}
    (book : Meter (List (Word w))) (old : Unit→Meter A)
    (acquire : Meter (List (Word w))→Meter (Option A))
    (nonempty : book.result≠[]) (val : A) (found : (acquire book).result=some val) :
    dispatchBook book old acquire=⟨val,(acquire book).steps+6⟩ := by
  rw [dispatchBook]
  cases eq : book.result with
  | nil => exact (nonempty eq).elim
  | cons b bs =>
    rw [show attemptedOr (acquire book) old=⟨val,(acquire book).steps+3⟩ from
      attemptedOr_success _ _ _ found]

theorem nonempty_book_failure {A : Type} {w : ℕ}
    (book : Meter (List (Word w))) (old : Unit→Meter A)
    (acquire : Meter (List (Word w))→Meter (Option A))
    (nonempty : book.result≠[]) (missing : (acquire book).result=none) :
    dispatchBook book old acquire=⟨(old ()).result,(acquire book).steps+(old ()).steps+7⟩ := by
  rw [dispatchBook]
  cases eq : book.result with
  | nil => exact (nonempty eq).elim
  | cons b bs =>
    change (⟨(attemptedOr (acquire book) old).result,(attemptedOr (acquire book) old).steps+3⟩ :
      Meter A)=_
    rw [attemptedOr,missing]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

def storedBook (site : StoredSite T v key prec tw bw page) : Meter (List (Word site.birth.port)) :=
  selectedEdgeBook site.birth.native.gWord site.birth.native.physical.raw

theorem stored_book_actual (site : StoredSite T v key prec tw bw page) :
    let J := site.birth.native
    let out := storedBook site
    let ord := actualEdgeOrder T v J.physical
    out.result=List.ofFn (fun j=>childKey T v J.physical (ord j)) ∧
      out.result.Nodup ∧
      out.steps≤7+(J.physical.raw.map J6R25PreparedSupply.rowScanFee).sum+
        v.child.edges*(4*site.birth.port+5) :=
  exact_child_edge_book T v site.birth.native

theorem stored_book_length (site : StoredSite T v key prec tw bw page) :
    (storedBook site).result.length=v.child.edges := by
  rw [(stored_book_actual site).1,List.length_ofFn]

theorem stored_book_empty_iff (site : StoredSite T v key prec tw bw page) :
    (storedBook site).result=[] ↔ v.child.edges=0 := by
  rw [← stored_book_length site]
  exact List.length_eq_zero_iff.symm

structure ResidentLeafData (site : StoredSite T v key prec tw bw page) where
  own : ℕ
  lines : List (ResidentPort own site.birth.port)
  table : OriginTable own site.birth.port key prec page
  roster : List (Word own)

def storedAttempt (site : StoredSite T v key prec tw bw page) (D : ResidentLeafData site)
    (F : Frame f v.child.prec) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (book : Meter (List (Word site.birth.port))) : Meter (Option (Block F ell)) :=
  onlineLeaf hf F pos B v.child.edges v.child.edges book D.lines D.table D.roster

def storedLeaf (site : StoredSite T v key prec tw bw page) (D : Unit→ResidentLeafData site)
    (F : Frame f v.child.prec) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (old : Unit→Meter (Block F ell)) : Meter (Block F ell) :=
  dispatchBook (storedBook site) old (fun book=>storedAttempt site (D ()) F pos B book)

theorem stored_zero_preserves_read (site : StoredSite T v key prec tw bw page)
    (D : Unit→ResidentLeafData site) (F : Frame f v.child.prec) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page) (old : Unit→Meter (Block F ell))
    (empty : v.child.edges=0) :
    storedLeaf site D F pos B old=
      ⟨(old ()).result,(storedBook site).steps+(old ()).steps+3⟩ :=
  empty_book_preserves_leaf _ _ _ ((stored_book_empty_iff site).mpr empty)

theorem stored_positive_fee (site : StoredSite T v key prec tw bw page)
    (D : Unit→ResidentLeafData site) (F : Frame f v.child.prec) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page) (old : Unit→Meter (Block F ell))
    (positive : 0<v.child.edges) (val : Block F ell)
    (found : (storedAttempt site (D ()) F pos B (storedBook site)).result=some val) :
    storedLeaf site D F pos B old=
      ⟨val,(storedAttempt site (D ()) F pos B (storedBook site)).steps+6⟩ :=
  nonempty_book_success _ _ _
    (fun h=>(Nat.ne_of_gt positive) ((stored_book_empty_iff site).mp h)) val found

end
#print axioms empty_book_preserves_leaf
#print axioms nonempty_book_success
#print axioms nonempty_book_failure
#print axioms stored_book_actual
#print axioms stored_book_empty_iff
#print axioms stored_zero_preserves_read
#print axioms stored_positive_fee
end J6R51Leaf
