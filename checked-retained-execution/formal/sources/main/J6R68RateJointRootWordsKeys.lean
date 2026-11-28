import J6R68RateJointRootWordsBody
import J6R55TerminalBootJoinedCore

/-! Bind concrete replay to the first source state of the joined paid
machine, and tie public issuer cost to the same original exterior address.
The retained template table is not assumed to have exactly one row/slot. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R21Ancestor J6R27OriginalGate
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R35RootOrigins
open J6R26DescriptorTree J6R33GeneratedChildSite J6R33StatefulArithmeticPage J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R55BootBodies J6R58BootScope J6R57ScopeFee J6R30ProducedGateRegistry
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R55TerminalBootJoined J6R51Online J6R31RootResidentTables J6R32StatefulArithmetic
open J6R54ExteriorOwner J6R53OldOwnerRoot J6R55TerminalOrigin J6R50SourceProducer

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5100
set_option maxHeartbeats 10500000
set_option Elab.async false
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "RootSlot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "TicketAt" => (fun w : RootSlot=>(Path.root : Path sel Ext Ext).ticket w)
local notation "InputAt" => (fun w : RootSlot=>OccurrenceInput T (TicketAt w) key prec tw bw Pg)

variable (K : ResidentFirstTemplates X pad T)

theorem actual_first_handle_keys_injective : Function.Injective K.keys := by
  intro u v eq
  have h := K.hit u
  rw [eq,K.hit v] at h
  exact (congrArg Sigma.fst (Option.some.inj h)).symm

theorem exactly_indexed_first_table_count (order : List RootSlot)
    (unique : order.Nodup) (full : ∀ w,w∈order)
    (normal : K.raw=order.map (fun w=>(⟨K.keys w,⟨w,K.template w⟩⟩ :
      RefRow K.keyWidth (Sigma InputAt)))) :
    K.raw.length=Nat.card RootSlot ∧ (K.raw.map RefRow.address).Nodup := by
  letI : Fintype RootSlot := (Plan sel).finiteSlot Ext
  rw [normal,List.length_map,List.map_map]
  exact ⟨full_roster_length order unique full,unique.map (actual_first_handle_keys_injective X pad K)⟩

#print axioms actual_first_handle_keys_injective
#print axioms exactly_indexed_first_table_count
end
end J6R68RateJoint.RootWords
