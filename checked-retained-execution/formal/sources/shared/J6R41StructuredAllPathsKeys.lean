import J6R34RootAtlasOccurrence
import J6R41StructuredAllPathsSite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000
set_option maxRecDepth 3000

/-! Native key identity for the genuine R34 compiler. This chooses
the canonical key from the real physical Page indexing used by that
source compiler; the width transport cannot change its payload bits.
It does not synthesize the later chart's raw position or group word. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R21Ancestor J6R34ChildPath J6R26DescriptorTree J6R15ModeCost
open J6R36ChildFramedRoute J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R25PreparedSupply J6R30ProducedGateRegistry J6R34RootAtlas
open J6R32ChildResidentTransfer J6R33GeneratedChildSite

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}

def occurrencePageKey (I : OccurrenceInput T ticket key prec tw bw page) (k : PageAt T ticket) : Word page :=
  cast (congrArg Word I.width) (childPageKey (I.q-dim ticket) k)

theorem cast_word_preserves_bits {a b : ℕ} (e : a=b) (w : Word a) :
    (cast (congrArg Word e) w).bits=w.bits := by
  subst b
  rfl

theorem literal_page_key_bytes (I : OccurrenceInput T ticket key prec tw bw page) (k : PageAt T ticket) :
    (occurrencePageKey I k).bits=(childPageKey (I.q-dim ticket) k).bits :=
  cast_word_preserves_bits I.width _

private theorem cast_page_lookup {a b : ℕ}
    (w : a=b) (B : Birth T ticket key prec tw bw a) (x : Word a) :
    let C : Birth T ticket key prec tw bw b := w ▸ B
    (locate (cast (congrArg Word w) x) C.rows).result.isSome=(locate x B.rows).result.isSome := by
  subst b
  rfl

theorem actual_native_page_key_hits (I : OccurrenceInput T ticket key prec tw bw page)
    (k : PageAt T ticket) :
    (locate (occurrencePageKey I k) (compileOccurrence I).rows).result.isSome = true := by
  let A := Classical.choice (occurrence_real_receipt I)
  let issued := A1R12.padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let B := issuedBirth I.native.result issued I.words.result I.hOld A
  have eq := cast_page_lookup I.width B (childPageKey (I.q-dim ticket) k)
  have hit : (locate (childPageKey (I.q-dim ticket) k) B.rows).result.isSome=true := by
    change (locate (childPageKey (I.q-dim ticket) k) A.bank).result.isSome=true
    rw [A.lookup k]
    rfl
  exact eq.trans hit

theorem actual_native_key_hits_same_immutable (I : OccurrenceInput T ticket key prec tw bw page)
    (k : PageAt T ticket) :
    (locate (occurrencePageKey I k) (compileOccurrence I).job.immutable.payload.payload.pages).result.isSome=true :=
  actual_native_page_key_hits I k

#print axioms literal_page_key_bytes
#print axioms actual_native_page_key_hits
#print axioms actual_native_key_hits_same_immutable
end J6R41StructuredAllPaths