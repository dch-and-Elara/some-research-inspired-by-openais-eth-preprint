import J6R53TerminalExteriorOldRows
import J6R53TerminalGateWhole

/-! Positive-stop source evaluation after all genuinely mounted owner
bytes. The only old-side proof input is source provenance (not an
executable LeafChart, supplied dispatch, or entry values). -/
namespace J6R53TerminalExterior
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R50Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 46000000
set_option maxRecDepth 6000
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
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

theorem actual_source_terminal_from_owner_provenance
    (saved : CachedParentFrames (sourceState M p w).site)
    (headers : ParentOwnerHeaders (sourceState M p w).site)
    (gates : c.host.Row⊕c.host.Col→Option (CodeGate (Word (pageKeyWidth m+a m))))
    (roster : CompleteRoster (sourceState M p w).site.oldKey (parentData (sourceState M p w) gates))
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (hBase : 0<base) {b : ℕ} (hb : 0<b) (fit : (p.ticket w).child.edges≤2^b)
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B)
    (live : opened (borns M) rootLive (.step p w) B)
    (F : Frame f (p.ticket w).child.prec)
    (origin : ∀ x : OldAt T (p.ticket w),KnownOldOrigin X M p w x (gates x.val)) :
    let site := sourceState M p w
    let out := meteredTerminalFromOwners site saved headers.raw roster.raw b F B
    ∃ word,out.result=some word ∧ F.decode word=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) := by
  let site := sourceState M p w
  let v := p.ticket w
  have younger : OnPath (borns M) site.birth.job (.step p w) := OnPath.youngest p w rfl
  refine acquired_terminal_from_real_owner_rows site saved headers gates roster inj b
    (.step p w) (borns M) younger rootLive B live F ?_
  intro old
  let u := physicalChildRows (T:=T) (v:=v) old
  exact actual_old_origin_compiles_and_evaluates X M p w old (gates u.val) (origin u)
    saved inj hBase hb fit rootLive B openRoot live.1 F

end
#print axioms actual_source_terminal_from_owner_provenance
end J6R53TerminalExterior
