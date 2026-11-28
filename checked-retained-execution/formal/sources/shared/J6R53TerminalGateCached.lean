import J6R53TerminalGateRouting
import J6R52TerminalAncestorFrames
import J6R50LeafRead

/-! The original compact opcode for this old owner is read on the real
retained cache. Signed literal order is kept, and the current physical
keys and ordinal words are derived by metered scans from that same
cache rather than imported from a prepared LeafChart. -/
namespace J6R53TerminalGate
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R34ChildPath J6OrientedHost J6R50Leaf J6R52Terminal J6R51ParentFrames
open J6R26DescriptorTree J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6ActiveRun
open J6R50SourceProducer J6R21Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 34000000
set_option maxRecDepth 4700
set_option Elab.async false

def compileSavedGate {w W owner key prec page : ℕ} (b : ℕ)
    (book : List (Word W)) (frames : List (FramedEdge W owner key prec page))
    (old : Word owner) (gate : CodeGate (Word w)) : Meter (Option (ReadCmd key page)) :=
  let calls := collectRetained old frames
  let index := suffixTable w calls.result
  let out := rerouteGate index.result gate
  match out.result with
  | none => ⟨none,calls.steps+index.steps+out.steps+4⟩
  | some new =>
    let compiled := compileCurrentGate b book new
    ⟨compiled.result.map (ReadCmd.gate b),calls.steps+index.steps+out.steps+compiled.steps+7⟩

private theorem sum_constant_counts {A : Type} (xs : List A) (n : ℕ) :
    (xs.map (fun _=>n)).sum=xs.length*n := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul]
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,ih]
    omega

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

theorem compile_actual_saved_gate {w b d : ℕ} (hb : 0<b) (fit : v.child.edges≤2^b)
    (site : StoredSite T v key prec tw bw page) (saved : CachedParentFrames site.site)
    (inj : Function.Injective site.site.oldKey) (u : OldAt T v)
    {root : Point f ell} (tr : Trace root (point v.parent.host u.val))
    (seed : PortAt root→Word w) (unique : Function.Injective seed)
    (body : ∀ p : PortAt (point v.parent.host u.val),
      (site.birth.native.physical.record p.val).body=tr.literal (fun x=>(seed x).bits) p)
    (scope : Fin d→PortAt root) (g : Gate d) :
    let book := cachedBook site saved
    let ports := keptPorts T v site.birth.native.physical u
    let ord := retainedEdgeOrder T v site.birth.native.physical u
    let t := tr.keep (retainedMove T v u)
    let old := site.site.oldKey u.val
    let out := compileSavedGate b book.result saved.rows old (encodeGate (seed∘scope) g)
    out.result=some (ReadCmd.gate b
      (forgetGate (gateTape fit (tracedSlot t ord∘scope) g))) ∧
    out.steps≤(collectRetained old saved.rows).steps+3+
      ports.length*(17+8*w+3*site.birth.port+5*t.depth)+
      (8+d*(locateFee w ports.length+site.birth.port+9))+
      currentGateFee site.birth.port b v.child.edges d+7 := by
  let J := site.birth.native
  let old := site.site.oldKey u.val
  let ps := keptPorts T v J.physical u
  let t := tr.keep (retainedMove T v u)
  let ord := retainedEdgeOrder T v J.physical u
  let names (j : Fin v.child.edges) := (J.physical.record (ord j).val).address
  let bodyName (p : PortAt (retainedMove T v u).next) := (J.physical.record (edge p.val).val).address
  let bSeed (p : PortAt (retainedMove T v u).next) := seed (t.back p)
  let scopeNow (j : Fin d) := t.back.symm (scope j)
  let req := collectRetained old saved.rows
  let book := cachedBook site saved
  have reqs :=
    cached_retained_requests_same_actual_ports site saved inj u tr (fun x=>(seed x).bits) body
  have reqExact : req.result=ps.map (fun p=>⟨bodyName p,List.replicate t.depth false++(bSeed p).bits⟩) := by
    refine reqs.trans ?_
    apply List.map_congr_left
    intro p _
    change WireRequest.mk (bodyName p) (t.literal (fun x=>(seed x).bits) p)=_
    rw [t.literal_exact]
  have mounted : (suffixTable w req.result).result=ps.map (fun p=>⟨bSeed p,bodyName p⟩) := by
    rw [reqExact,suffix_table_exact]
  have tableFee : (suffixTable w req.result).steps=3+ps.length*(17+8*w+3*site.birth.port+5*t.depth) := by
    rw [reqExact,suffix_table_exact]
    simp only [List.length_replicate,sum_constant_counts]
    all_goals rfl
  have trScope : bSeed∘scopeNow=seed∘scope := by
    funext j
    exact congrArg seed (t.back.apply_symm_apply (scope j))
  have hNames : bodyName∘scopeNow = names∘(tracedSlot t ord∘scope) := by
    funext j
    change (J.physical.record (edge (t.back.symm (scope j)).val).val).address =
      (J.physical.record (ord (ord.symm (edge (t.back.symm (scope j)).val))).val).address
    rw [Equiv.apply_symm_apply]
  have ua := (kept_ports_exact T v J.physical u).2
  have routeLaw :=
    reroute_actual_gate ps bSeed (unique.comp t.back.injective) bodyName scopeNow (fun j=>ua (scopeNow j)) g
  dsimp only at routeLaw
  rw [trScope,hNames] at routeLaw
  have bij : Function.Injective names :=
    J.physical.distinct.comp (Subtype.val_injective.comp ord.injective)
  have keys : book.result=List.ofFn names :=
    (cached_book_exact site saved).1.trans (exact_child_edge_book T v J).1
  have comp := current_source_gate hb fit book.result names bij keys (tracedSlot t ord∘scope) g
  let index := suffixTable w req.result
  let route := rerouteGate index.result (encodeGate (seed∘scope) g)
  have hit : route.result=some (encodeGate (names∘(tracedSlot t ord∘scope)) g) := by
    unfold route index
    rw [mounted]
    exact routeLaw.1
  have routeFee : route.steps≤8+d*(locateFee w ps.length+site.birth.port+9) := by
    unfold route index
    rw [mounted]
    exact routeLaw.2
  change (compileSavedGate b book.result saved.rows old (encodeGate (seed∘scope) g)).result=_ ∧ _
  unfold compileSavedGate
  dsimp only
  rw [show (rerouteGate (suffixTable w req.result).result (encodeGate (seed∘scope) g)).result=_ from hit]
  dsimp only
  refine ⟨?_,?_⟩
  · rw [comp.1]
    rfl
  · change req.steps+index.steps+route.steps+
        (compileCurrentGate b book.result (encodeGate (names∘(tracedSlot t ord∘scope)) g)).steps+7≤
        req.steps+3+ps.length*(17+8*w+3*site.birth.port+5*t.depth)+
          (8+d*(locateFee w ps.length+site.birth.port+9))+currentGateFee site.birth.port b v.child.edges d+7
    change index.steps=_ at tableFee
    rw [tableFee]
    have h := comp.2
    omega

end
#print axioms compile_actual_saved_gate
end J6R53TerminalGate
