import J6R54TerminalBootFirstTerminal
import J6R54TerminalBootLiteralMount

/-! Attachment to the unchanged R54 terminal: create the first owner
roster by reading the same already-live bank passed to the terminal,
then use the existing paid rekeys. No installation occurs here. The
proof does not infer first-site raw tags or bodies from key equality. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R34RootAtlas J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R53TerminalGate J6R53TerminalExterior J6R41StructuredAllPaths
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 48000000
set_option maxRecDepth 6500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)
local notation "r" => (exteriorChild G ell X.centre X.sample X.group)


variable {rootName : SourceVertex P→Word own}

structure InstalledOwnerInputs where
  source : RootRoster (P:=P) gate pad rootName
  keys : ∀ w : (Plan sel).Slot r, KeyInputs X gate pad source (M.initial w).result.site.oldKey
  distinct : Function.Injective rootName
  steps : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (incoming : RosterAt M (bootGates X) p w) (u : (Plan sel).Slot (p.ticket w).child),
    ActualOwnerWords M (bootGates X) p w incoming u

def measured_first_from_installed_atlas
    (A : InstalledOwnerInputs (rootName:=rootName) X M gate)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B) :
    FirstRosterAndRekeys X M gate where
  first w := mountFirstOwners X gate pad A.source B openRoot (A.keys w) A.distinct
  steps := A.steps

theorem same_first_raw_and_fee_from_one_bank
    (A : InstalledOwnerInputs (rootName:=rootName) X M gate)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B) (w : (Plan sel).Slot r) :
    let read := chosenFirstRaw X gate pad A.source B (M.initial w).result.site.oldKey (A.keys w)
    let loaded := runRosterAlong M (bootGates X)
      (roster_program_from_measured_first X M gate boot
        (measured_first_from_installed_atlas X M gate A B openRoot)) .root w
    read.result=some loaded.result.raw ∧ loaded.steps=(A.keys w).headers.steps+read.steps :=
  literal_public_mount_reads_the_same_live_atlas X gate pad A.source B openRoot
    (M.initial w).result.site.oldKey (A.keys w) A.distinct

theorem terminal_from_same_installed_atlas_and_measured_rekeys
    (A : InstalledOwnerInputs (rootName:=rootName) X M gate)
    (gateWidth : gate.created.val=base)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (saved : CachedParentFrames (sourceState M p w).site)
    (hBase : 0<base) {b : ℕ} (hb : 0<b) (fit : (p.ticket w).child.edges≤2^b)
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B)
    (live : opened (borns M) rootLive (.step p w) B)
    (groups : Meter (List (Word 6)))
    (groupLaw : groups.result=(runRosterAlong M (bootGates X)
      (roster_program_from_measured_first X M gate boot
        (measured_first_from_installed_atlas X M gate A B openRoot)) p w).result.order.map
      (fun v=>(ownerGroupRow (sourceState M p w).site v).group))
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (F : Frame f (p.ticket w).child.prec) :
    let exactFirst := measured_first_from_installed_atlas X M gate A B openRoot
    let prog := roster_program_from_measured_first X M gate boot exactFirst
    let out := meteredTerminalAfterRosterHistory X M prog p w saved groups groupLaw b F B
    ∃ word,out.result=some word ∧ F.decode word=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) :=
  terminal_from_first_raw_roster_and_measured_rekeys X M gate boot
    (measured_first_from_installed_atlas X M gate A B openRoot)
    gateWidth p w saved groups groupLaw inj hBase hb fit rootLive B openRoot live F

end
#print axioms measured_first_from_installed_atlas
#print axioms same_first_raw_and_fee_from_one_bank
#print axioms terminal_from_same_installed_atlas_and_measured_rekeys
end J6R54TerminalBoot
