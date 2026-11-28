import J6R58BootScopeGeometry
import J6R58BootScopeResident

/-! The joined first-slot debit contains the actual physical writer
exactly once, then the read-only mount and the actual addon emission.
Issuance carries the copied result, not another physical-writer fee.
These are the local boot charges, not a billed whole DFS. -/
namespace J6R58BootScope
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online J6R55TerminalOrigin J6R54TerminalBoot J6R55BootBodies
open J6R55TerminalBootJoined J6R57ScopeFee J6R48GeneratedAddons J6R53OldOwner
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000
set_option maxRecDepth 6100
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)




local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "InputAt" => (fun w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))=>
  OccurrenceInput T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad))

structure ResidentFirstTemplates (T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf) where
  keyWidth : ℕ
  keys : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))→Word keyWidth
  raw : List (RefRow keyWidth
    (Sigma (fun w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))=>OccurrenceInput T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad))))
  template : ∀ w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)),OccurrenceInput T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad)
  hit : ∀ w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)),(locate (keys w) raw).result=some ⟨w,template w⟩
  order : ∀ w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)),(template w).geometry.edges=orderedExteriorEdges X

variable (K : ResidentFirstTemplates X pad T)
variable (L : BootLaneTape X gate pad)

def fetchedFirstTemplate (w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))) : Meter (InputAt w) :=
  checkedBootHandle (T:=InputAt) K.raw (K.keys w) w (K.template w) (K.hit w)

theorem fetched_first_template_same_chart (w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))) :
    (fetchedFirstTemplate X pad K w).result=K.template w :=
  (checked_boot_handle_retains_actual_source (T:=InputAt) K.raw (K.keys w) w (K.template w) (K.hit w)).1

def firstBodiesFromPaidBootCache : FirstBodyProgram X gate pad T :=
  firstBodiesFromSameResident (sel:=sel) (T:=T) X gate pad L (fetchedFirstTemplate X pad K)
    (fun w=> (congrArg (fun I : InputAt w=>I.geometry.edges)
      (fetched_first_template_same_chart X pad K w)).trans (K.order w))

def paidFirstOwnerKeys {width : ℕ}
    {name : (Ext).host.Row⊕(Ext).host.Col→Word width}
    (Y : KeyInputs X gate pad root name) : KeyInputs X gate pad root name :=
  { headers := copyBootHeaders Y.headers.result
    headerExact := (congrArg Meter.result (copy_boot_headers_exact _)).trans Y.headerExact
    dest := copyGateKeys Y.dest.result
    destExact := (congrArg Meter.result (copy_gate_keys_exact _)).trans Y.destExact }

variable (D : OwnerWordsAtBodies X gate pad root (firstBodiesFromPaidBootCache X gate pad K L))
variable (Q : ∀ w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)),ResidentBootQueries (D.ports w))

def paidFirstOwnerWords : OwnerWordsAtBodies X gate pad root (firstBodiesFromPaidBootCache X gate pad K L) :=
  { width := D.width
    name := D.name
    distinct := D.distinct
    keys := fun w=>paidFirstOwnerKeys X gate pad root (D.keys w)
    ports := fun w=>paidResidentBootPorts (D.ports w) (Q w) }

def rawFirstInputGeometry (templateWidth templateRows own headers owner destRows seatKey seats dim pg port edges : ℕ) :=
  (locateFee templateWidth templateRows+3*templateWidth+5)+(3+(3*own+26)*headers)+
    (3+(3*owner+5)*destRows)+(3+(3*seatKey+3*dim+3*pg+48)*seats)+
    (2*edges)*(locateFee port (2*edges)+3*port+3*owner+3*seatKey+9)

end
#print axioms fetchedFirstTemplate
#print axioms fetched_first_template_same_chart
#print axioms firstBodiesFromPaidBootCache
#print axioms paidFirstOwnerKeys
#print axioms paidFirstOwnerWords
#print axioms rawFirstInputGeometry
end J6R58BootScope
