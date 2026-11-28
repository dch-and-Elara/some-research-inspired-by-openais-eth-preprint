import J6R55TerminalOriginSite
import J6R54ExteriorOwnerMount

/-! The old and page tags of one genuine exterior first slot originate
in the completed read-only first owner mount. The caller supplies
the measured slot occurrence and the physical address tables, not
a prebuilt origin function or a proof that arbitrary StoredSite tags match. -/
namespace J6R55TerminalOrigin
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 32000000
set_option maxRecDepth 6000
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)



variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))

structure LiteralFirstSlot (T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf) where
  occurrence : Meter (OccurrenceInput T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad))
  width : ℕ
  name : ((exteriorChild G ell X.centre X.sample X.group).host.Row ⊕
    (exteriorChild G ell X.centre X.sample X.group).host.Col)→Word width
  injective : Function.Injective name
  keys : KeyInputs X gate pad root name
  words : BootPortWords occurrence.result name

variable (D : LiteralFirstSlot X gate pad root w T)
variable (B : (PageBank f ell key prec tw bw (pageKeyWidth m+pad))) (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)

def assembleFirstExterior :
    Meter (StoredSite T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad)) :=
  let mounted := mountFirstOwners X gate pad root B live D.keys rootInj
  assembleOriginSite (exterior_data_origin X gate pad) D.injective D.occurrence mounted D.words

theorem actual_first_exterior_tags :
    (assembleFirstExterior X gate pad root w D B live rootInj).result.origins=initialOrigin X gate pad := rfl

theorem actual_first_exterior_occurrence :
    (assembleFirstExterior X gate pad root w D B live rootInj).result.input=D.occurrence.result := rfl

theorem actual_first_exterior_cost :
    let mounted := mountFirstOwners X gate pad root B live D.keys rootInj
    let out := assembleFirstExterior X gate pad root w D B live rootInj
    out.steps=D.occurrence.steps+mounted.steps+D.words.seats.steps+
      (projectOriginTape mounted.result.raw).steps+
      (J6R48GeneratedAddons.emit (readBootAddon D.words mounted.result)
        (compileOccurrence D.occurrence.result).native.physical.order).steps := rfl

end
#print axioms assembleFirstExterior
#print axioms actual_first_exterior_tags
#print axioms actual_first_exterior_occurrence
#print axioms actual_first_exterior_cost
end J6R55TerminalOrigin
