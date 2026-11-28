import J6R52TerminalFreshCore

/-! Compile every actual new Page, including pages with no incident
wire. The only roster consumed by the runtime is the recorded key
sequence of the same published occurrence. The book is read once. -/
namespace J6R52Terminal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths J6R51ParentFrames
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun J6R49SourceLayout J6R50SourceProducer J6R51Leaf J6R50Leaf
open J6R32ChildResidentTransfer P11FullPacking
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16500000
set_option maxRecDepth 3500
set_option Elab.async false

theorem gather_key_roster {A B D : Type*} (stride : ℕ) (read : B→Meter (Option D))
    (key : A→B) (items : List A) :
    gatherOptions stride read (items.map key)=
      gatherOptions stride (fun x=>read (key x)) items := by
  induction items with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons,gatherOptions,ih]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (site : StoredSite T v key prec tw bw page)
variable (saved : CachedParentFrames site.site)

def trueFreshPages (_site : StoredSite T v key prec tw bw page) : List (PageAt T v) :=
  orderedChildPages ((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth)
    (layout T v).copies

def compileAllFresh : Meter (Option (List (ReadCmd key page))) :=
  let a := readBankKeys site.birth.rows
  let book := cachedBook site saved
  let comp := gatherOptions 1 (compileFreshOne site.birth.job.identifier book.result saved.rows) a.result
  ⟨comp.result,a.steps+book.steps+comp.steps+7⟩

def freshItemFee (k : PageAt T v) : ℕ :=
  let pg := occurrencePageWord site.input k
  3+(saved.rows.map (freshVisitFee pg)).sum+
    (4+((freshList site k).map (fun h=>sourceWireFee site.birth.port
      (freshOrdinal site k h).val (freshBody h).length)).sum)+(3*key+1)+(3*page+1)+7

theorem all_fresh_commands_from_actual_paid_roster :
    let out := compileAllFresh site saved
    out.result=some ((trueFreshPages site).map (freshWord site)) ∧
      out.steps=(3+(3*page+7)*site.birth.rows.length)+(cachedBook site saved).steps+
        (3+((trueFreshPages site).map (fun k=>freshItemFee site saved k+7)).sum)+7 := by
  let pg := occurrencePageWord site.input
  let book := cachedBook site saved
  let lookup := readBankKeys site.birth.rows
  let one := compileFreshOne site.birth.job.identifier book.result saved.rows
  obtain ⟨keys,_,len⟩ := compiled_occurrence_has_full_ordered_keys site.input
  have rok : lookup.result=(trueFreshPages site).map pg := keys
  have paid : lookup.steps=3+(3*page+7)*site.birth.rows.length := len
  have h (k : PageAt T v) : (one (pg k)).result=some (freshWord site k) ∧
      (one (pg k)).steps=freshItemFee site saved k := compile_cached_fresh_one site saved k
  have run := gather_options_exact 1 (fun k=>one (pg k)) (freshWord site) (trueFreshPages site)
    (fun k _=>(h k).1)
  have E : (trueFreshPages site).map (fun k=>(one (pg k)).steps+1+6)=
      (trueFreshPages site).map (fun k=>freshItemFee site saved k+7) := by
    apply List.map_congr_left
    intro k _
    rw [(h k).2]
  dsimp only [compileAllFresh]
  rw [show (readBankKeys site.birth.rows).result=_ from rok,
    show (readBankKeys site.birth.rows).steps=_ from paid,
    gather_key_roster,run,E]
  exact ⟨rfl,rfl⟩

end
#print axioms gather_key_roster
#print axioms all_fresh_commands_from_actual_paid_roster
end J6R52Terminal
