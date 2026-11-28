import J6R54TerminalBootOnline
import J6R54TerminalBootSeed
import J6R53TerminalExteriorComposition
import J6R53TerminalExteriorWhole

/-! A single actual printed first payload, not a supplied per-row
provenance chart, now determines all old source lineages on the
actual online recursion. Combine with the R53 terminal program
without modifying its raw implementation or claimed fees. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 45000000
set_option maxRecDepth 6300
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (gate : Stamp key prec)

structure ExactPrintedBoot : Prop where
  origins : ∀ w,(M.initial w).result.origins=initialOrigin X gate pad
  bodies : ∀ w h,((M.initial w).result.birth.native.physical.record h).body=
    (initialPayload X gate pad h).2

variable (boot : ExactPrintedBoot X M gate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

include boot in
theorem actual_old_sources_from_one_printed_boot (gateWidth : gate.created.val=base)
    (u : OldAt T (p.ticket w)) :
    KnownOldOrigin X M p w u (gateHistory T (bootGates X) p u.val) := by
  have joint := actual_online_gate_and_origin_are_joint M (initialOrigin X gate pad)
    (initialPayload X gate pad) (bootGates X) boot.origins boot.bodies
    (exact_boot_port_uses_the_same_owner_tag X gate pad gateWidth) p w u.val
  rcases joint with outside|inside
  · obtain ⟨A,codeThere⟩ := outside
    rcases exact_initial_payload_gate_or_page X gate pad gateWidth A.vertex with older|page
    · obtain ⟨x,t,codeHere,bodyAt⟩ := older
      have whole := actual_birth_prefix_extends_the_exterior_seed M p w u.val A (rootGateBody x) t
        (fun h=>congrArg Prod.snd (bodyAt h))
      exact .original x (J6R35RootOrigins.concatenate t A.trace) whole (codeThere.trans codeHere)
    · obtain ⟨k,t,codeHere,tagAt,bodyAt⟩ := page
      have whole := actual_birth_prefix_extends_the_exterior_seed M p w u.val A
        (originSeed (rootChart P) (oddAxis m) X.group k) t (fun h=>congrArg Prod.snd (bodyAt h))
      exact .exterior k (J6R35RootOrigins.concatenate t A.trace) (A.tag.trans tagAt)
        whole (codeThere.trans codeHere)
  · obtain ⟨inner,noGate⟩ := inside
    obtain ⟨A⟩ := inner
    exact .native A noGate

include boot in
theorem actual_terminal_on_one_printed_boot
    (gateWidth : gate.created.val=base)
    (saved : CachedParentFrames (sourceState M p w).site)
    (headers : ParentOwnerHeaders (sourceState M p w).site)
    (roster : CompleteRoster (sourceState M p w).site.oldKey
      (parentData (sourceState M p w) (gateHistory T (bootGates X) p)))
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (hBase : 0<base) {b : ℕ} (hb : 0<b) (fit : (p.ticket w).child.edges≤2^b)
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B)
    (live : opened (borns M) rootLive (.step p w) B)
    (F : Frame f (p.ticket w).child.prec) :
    let site := sourceState M p w
    let out := meteredTerminalFromOwners site saved headers.raw roster.raw b F B
    ∃ word,out.result=some word ∧ F.decode word=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) :=
  actual_source_terminal_from_owner_provenance X M p w saved headers _ roster inj hBase hb fit
    rootLive B openRoot live F (actual_old_sources_from_one_printed_boot X M gate boot p w gateWidth)

end
#print axioms actual_old_sources_from_one_printed_boot
#print axioms actual_terminal_on_one_printed_boot
end J6R54TerminalBoot
