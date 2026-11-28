import J6R53TerminalGateCached
import J6R53TerminalGateGeometry
import J6R37StructuredRootPorts
import J6R21AncestorOriginReads

/-! Specialization to the source's own printed stable-root prefix.
The root gate suffix is the real physical (page, slot), not the signed
half-address or the unrelated compact input column rank. -/
namespace J6R53TerminalGate
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6R15ModeCost J6R21Ancestor J6R27OriginalGate J6R21Leaf J6OrientedHost
open J6R35RootOrigins J6R37StructuredRoot J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6Mesh J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R24MeteredRecursion J6R22Active
open J6R50Leaf J6R50SourceProducer J6R51ParentFrames J6R52Terminal J6R30GeneratedRootLayout J6R24LegalLayout
open J6R33StatefulArithmeticPage
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 4100
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n : ℕ}
variable (P : Plant V m n)


variable {f : ℤ[X]} {ell s C key prec tw bw page base : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

theorem actual_cached_original_gate_read
    (hBase : 0<base) {b : ℕ} (hb : 0<b) (fit : v.child.edges≤2^b)
    (site : StoredSite T v key prec tw bw page) (saved : CachedParentFrames site.site)
    (inj : Function.Injective site.site.oldKey) (old : OldAt T v)
    (x : SourceVertex P)
    (trace : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) x) (J6R34ChildPath.point v.parent.host old.val))
    (raw : ∀ p : PortAt (J6R34ChildPath.point v.parent.host old.val),
      (site.birth.native.physical.record p.val).body=trace.literal (rootGateBody x) p)
    (F : Frame f v.child.prec) (B : PageBank f ell key prec tw bw page)
    (bits : Fin v.child.edges→Bool) :
    let D := originalPortGate P (J6R28GeneratedRootFrame.constantRootWord m) x
    let mounted := encodeGate (rootSuffixAt (f:=f) (ell:=ell) (base:=base) P x∘D.port) D.gate
    let out := compileSavedGate b (cachedBook site saved).result saved.rows (site.site.oldKey old.val) mounted
    let cur := (retainedMove T v old).next
    let ord := retainedEdgeOrder T v site.birth.native.physical old
    ∃ cmd,out.result=some cmd ∧
      F.decode ((cmd : ReadCmd key page).read hf F T.vPositive B (List.ofFn bits)).result =
        (entry cur).read hf v.child.prec (assignment cur.host.network (bits∘ord.symm) cur.vertex) := by
  let D := originalPortGate P (J6R28GeneratedRootFrame.constantRootWord m) x
  let t := trace.keep (retainedMove T v old)
  let ord := retainedEdgeOrder T v site.birth.native.physical old
  let tape := gateTape fit (tracedSlot t ord∘D.port) D.gate
  let cmd : ReadCmd key page := .gate b (forgetGate tape)
  have shaped : ∀ p : PortAt (J6R34ChildPath.point v.parent.host old.val),
      (site.birth.native.physical.record p.val).body=trace.literal (fun q=>(rootSuffixAt (f:=f) (ell:=ell) (base:=base) P x q).bits) p := raw
  have built := (compile_actual_saved_gate hb fit site saved inj old trace (rootSuffixAt (f:=f) (ell:=ell) (base:=base) P x)
    (actual_owned_root_suffix_injective P x) shaped D.port D.gate).1
  have hF : 0<f.natDegree := F.natDegree hf ▸ F.sizePos
  have value := (original_through_trace P (J6R28GeneratedRootFrame.constantRootWord m)
    hf hBase F.hp hF T.vPositive F.sizePos F.exactMod x t ord fit tape rfl bits).1
  refine ⟨cmd,built,?_⟩
  let R : PageReadCode v.child.edges key page := .original b tape
  change F.decode ((eraseCode R).read hf F T.vPositive B (List.ofFn bits)).result=_
  rw [erase_read_exact]
  exact (boxTransport_cast F.exactMod _).trans value
end
#print axioms actual_cached_original_gate_read
end J6R53TerminalGate
