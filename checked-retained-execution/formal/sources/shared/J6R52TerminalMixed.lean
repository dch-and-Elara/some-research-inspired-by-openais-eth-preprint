import J6R52TerminalFreshColumn
import J6R49SourceLayoutVertex
import J6R34ChildPathLeafOrder
import J6R50LeafOnline

/-! Splice the actual paid fresh compiler into the full terminal.
Only the retained old row preparation is still an input. The right
half of the leaf needs no supplied command, page order, or value law. -/
namespace J6R52Terminal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R22Active
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R41StructuredAllPaths
open J6R34ChildPath J6R49SourceLayout J6R50Leaf J6R50SourceProducer J6R51ParentFrames
open J6R48Leaf J6R51Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 4200
set_option Elab.async false

def visitFramesClock {A : Type} : List A→Meter (List Unit)
  | []=>⟨[],2⟩
  | _::xs=>
    let r := visitFramesClock xs
    ⟨()::r.result,r.steps+4⟩

theorem frame_clock_exact {A : Type} (xs : List A) :
    visitFramesClock xs=⟨List.replicate xs.length (),4*xs.length+2⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [visitFramesClock,ih,List.length_cons,List.replicate_succ]
    congr 1

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (site : StoredSite T v key prec tw bw page)
variable (saved : CachedParentFrames site.site)

def freshCode (k : PageAt T v) : PageReadCode v.child.edges key page :=
  .generated site.birth.job.identifier (occurrencePageWord site.input k) 0
    ((freshList site k).map (fun h=>⟨freshBody h,List.replicate (freshOrdinal site k h).val true⟩))

theorem fresh_code_is_erased_word (k : PageAt T v) :
    eraseCode (freshCode site k)=freshWord site k := rfl

theorem clock_from_actual_frame_has_all_bits :
    (visitFramesClock saved.rows).result.length=v.child.edges := by
  have h := exact_cached_frames site saved
  rw [frame_clock_exact,List.length_replicate]
  rw [h,List.length_map,half_order_length]

def meteredMixedTerminal (old : Meter (Option (List (ReadCmd key page))))
    (F : Frame f v.child.prec) (B : PageBank f ell key prec tw bw page) :
    Meter (Option (Block F ell)) :=
  match old.result with
  | none=>⟨none,old.steps+4⟩
  | some commands =>
    let new := compileAllFresh site saved
    match new.result with
    | none=>⟨none,old.steps+new.steps+6⟩
    | some data =>
      let clock := visitFramesClock saved.rows
      let run := runRows hf F T.vPositive B clock.result (commands++data)
      ⟨some run.result,old.steps+new.steps+clock.steps+run.steps+9⟩

theorem mixed_terminal_exact_runtime_bill (old : Meter (Option (List (ReadCmd key page))))
    (F : Frame f v.child.prec) (B : PageBank f ell key prec tw bw page)
    (older : List (ReadCmd key page)) (arrived : old.result=some older) :
    let new := compileAllFresh site saved
    let clock := visitFramesClock saved.rows
    let ready := (trueFreshPages site).map (freshWord site)
    let run := runRows hf F T.vPositive B clock.result (older++ready)
    meteredMixedTerminal site saved old F B=
      ⟨some run.result,old.steps+new.steps+clock.steps+run.steps+9⟩ := by
  dsimp only [meteredMixedTerminal]
  rw [arrived]
  dsimp only
  rw [(all_fresh_commands_from_actual_paid_roster site saved).1]

theorem true_mixed_terminal_from_only_old_rows
    (old : Meter (Option (List (ReadCmd key page))))
    (O : OldVertexKeys site.site)
    (oldCode : v.child.host.Row→PageReadCode v.child.edges key page)
    (oldMounted : old.result=some (O.rows.map (fun x=>eraseCode (oldCode x))))
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born site.birth.job path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    (F : Frame f v.child.prec)
    (oldLaw : ∀ (x : Fin v.child.edges→Bool) u,
      F.decode ((oldCode u).run hf F T.vPositive B (List.ofFn x)).result=
        (v.child.host.file (.inl u)).read hf v.child.prec (assignment v.child.host.network
          (x∘(actualEdgeOrder T v site.birth.native.physical).symm) (.inl u))) :
    let out := meteredMixedTerminal site saved old F B
    ∃ word,out.result=some word ∧ F.decode word=reduce v.child.prec f ell (v.child.host.contract hf) := by
  let V := (vertexKeysOfBirth site.site O site.canonical).result
  let names := V.order site.site
  let code (u : v.child.host.Row⊕v.child.host.Col) :=
    match u with
    | .inl u=>oldCode u
    | .inr p=>freshCode site (physicalChildCols (T:=T) (v:=v) p)
  let clock := visitFramesClock saved.rows
  have edgeCount : v.child.host.edgeCount=v.child.edges :=
    (stable_step cfg sel (stable_reachable cfg sel v.path T.rootStable) v.slot).edgeCount
  have Complete := V.valid_order site.site
  let D : PagedLeaf v.child key page :=
    ⟨edgeCount,clock.result,clock_from_actual_frame_has_all_bits site saved,names,Complete.1,Complete.2,code⟩
  have valves : ∀ bits z,
      F.decode (D.query hf F T.vPositive B z (List.ofFn bits)).result=
        (v.child.host.file z).read hf v.child.prec (assignment v.child.host.network
          (bits∘(actualEdgeOrder T v site.birth.native.physical).symm) z) := by
    intro bits z
    cases z with
    | inl x => exact oldLaw bits x
    | inr col =>
      have truePage := emitted_fresh_word_is_actual_child_column site col path born wasBorn rootLive B live F bits
      let k := physicalChildCols (T:=T) (v:=v) col
      change F.decode ((freshCode site k).run hf F T.vPositive B (List.ofFn bits)).result=_
      rw [← erase_read_exact (freshCode site k) hf F T.vPositive B (List.ofFn bits),
        fresh_code_is_erased_word]
      exact truePage
  have H := actual_paged_leaf_physical_order D hf F T.vPositive B
    (actualEdgeOrder T v site.birth.native.physical) valves
  have newPack := (all_fresh_commands_from_actual_paid_roster site saved).1
  have exactRows : (PagedLeaf.toRaw D).rows.map (fun x=>eraseCode x.2)=
      (O.rows.map (fun x=>eraseCode (oldCode x)))++((trueFreshPages site).map (freshWord site)) := by
    change (names.map (fun x=>(x,code x))).map (fun x=>eraseCode x.2)=_
    rw [List.map_map]
    unfold names VertexKeys.order
    rw [List.map_append,List.map_map,List.map_map]
    congr 1
    change (colsOfBirth (T:=T) (v:=v)).map
      (fun col=>eraseCode (freshCode site (physicalChildCols (T:=T) (v:=v) col)))=_
    unfold colsOfBirth trueFreshPages
    rw [List.map_map]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply,Equiv.apply_symm_apply,fresh_code_is_erased_word]
  have equal := run_rows_is_raw hf F T.vPositive B (PagedLeaf.toRaw D)
  rw [exactRows,raw_leaf_is_same_dispatch] at equal
  refine ⟨(D.execute hf F T.vPositive B).result,?_,H⟩
  dsimp only [meteredMixedTerminal]
  rw [oldMounted]
  dsimp only
  rw [newPack]
  dsimp only
  exact congrArg some (congrArg Meter.result equal)

end
#print axioms frame_clock_exact
#print axioms mixed_terminal_exact_runtime_bill
#print axioms true_mixed_terminal_from_only_old_rows
end J6R52Terminal
