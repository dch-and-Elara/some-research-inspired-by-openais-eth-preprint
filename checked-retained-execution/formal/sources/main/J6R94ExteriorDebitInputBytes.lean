import J6R94ExteriorDebitHeader
import J6R32ChildResidentTransferFormat
import J6R54ExteriorOwnerSource

/-! The complete next-layout target file comes from (i) all old
owner headers including isolated factors and (ii) every Page
of the very same already installed exterior atlas. The incidence
file uses the separately priced original root half-record scan. -/
namespace J6R94ExteriorDebit
open scoped Classical Polynomial
open J6R64Active J6R32StatefulArithmetic
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R19Retained
open J6R25PreparedSupply J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R31RootResidentTables J6R27OriginalGate J6Mesh J6R49SourceLayout
open J6R54ExteriorOwner J6R55BootBodies J6R41StructuredAllPaths
open J6R30GeneratedRootLayout J6R28GeneratedRootFrame J6R26StablePreparedRoot
open J6R37StructuredRoot J6R35RootOrigins J6R34ChildPath J6R36ChildFramedRoute
open J6R10Repack J6OrientedHost J6R24LegalLayout J6R26DescriptorTree
open J6R32ChildResidentTransfer J6R12CollisionGreedyStep J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R33StatefulArithmeticPage J6R30ProducedGateRegistry

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4300
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n base native : ℕ} {P : Plant V m n}
variable {f : ℤ[X]}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co dep edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co dep edgew tc tj key prec tw bw)
variable (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Edge" => ((Ext).host.Edge)
local notation "R" => ((Ext).host.Row)
local notation "C" => ((Ext).host.Col)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)
local instance rootEdge : Fintype Edge := (Ext).host.finiteEdge

variable {name : SourceVertex P→Word own}
variable (S : RootLayoutStock P name)

def oldWordAt (u : R) : Word own := name u.val

def trueOldKeyScan : Meter (List (Word own)) :=
  let heads := emitRootHeaders [] S.roles
  let keep := selectOwnerKeys X.address.group heads.result
  ⟨keep.result,heads.steps+keep.steps+3⟩

theorem real_old_roster_from_stock :
    let heads := emitRootHeaders [] S.roles
    (trueOldKeyScan X S).result=(stageOldOrder X S.order).map (oldWordAt (name:=name) X) ∧
    (trueOldKeyScan X S).steps=heads.steps+3+
      (3+(3*own+77)*S.order.length+(3*own+1)*(stageOldOrder X S.order).length) := by
  let heads := emitRootHeaders [] S.roles
  have A := actual_root_group_headers_and_charge X [] rfl name S.order
    (⟨S.roles,0⟩ : Meter (List (Word own×BootRole))) S.rolesExact
  have chosen : heads.result=S.order.map (ownerHeader name (actualGroup X)) := A.1
  have keys := exact_filter_group_keys name (actualGroup X) X.group S.order
  unfold trueOldKeyScan
  dsimp only
  change (selectOwnerKeys X.address.group heads.result).result=_ ∧ heads.steps+
    (selectOwnerKeys X.address.group heads.result).steps+3=_
  rw [chosen,actual_exterior_group_word X,select_owner_keys_exact,keys]
  simp only [List.length_map]
  refine ⟨rfl,?_⟩
  dsimp only [heads,stageOldOrder]
  omega

def currentPageKeys (x : StableExterior G ell q ro co dep edgew tc tj key prec tw bw)
    (p : ℕ) (bank : PageBank f ell key prec tw bw (pageKeyWidth m+p)) :
    Meter (Option (Stamp key prec×List (Word (pageKeyWidth m+p)))) :=
  readMountedOwners bank (x.seed p).identifier

def writeExteriorTargets
    (buf : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) : Meter (List Target) :=
  let old := trueOldKeyScan X S
  let pages := currentPageKeys X pad buf
  let cmd := writeTargets old.result ((pages.result.map Prod.snd).getD [])
  ⟨cmd.result,old.steps+pages.steps+cmd.steps+5⟩

def writeExteriorIncidences
    (buf : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) : Meter (Option (List Incidence)) :=
  let selected := readPublishedHalfRows X buf
  let scan := readHalfIncidences m pad S.names selected.result
  ⟨scan.result,selected.steps+scan.steps+4⟩

theorem true_exterior_incidence_after_named_stock
    (buf : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (ownHead : OwnsHeader X.header.result buf) :
    (writeExteriorIncidences X pad S buf).result=
      some ((orderedExteriorEdges X).map (fun e=>
        ((oldWordAt (name:=name) X ((Ext).host.network.row e)).bits,
          (bootPageKey X pad ((Ext).host.network.col e)).bits))) ∧
    (writeExteriorIncidences X pad S buf).steps≤publishedPortDebit m tc tj prec edgew (orderedExteriorEdges X).length+
      (3+halfPairLimit m pad own (2*M m)*(orderedExteriorEdges X).length)+4 := by
  let wordR := fun e : Edge=>oldWordAt (name:=name) X ((Ext).host.network.row e)
  let wordC := fun e : Edge=>bootPageKey X pad ((Ext).host.network.col e)
  have query (e : Edge) :
      (locate (halfPortSpec m (side e.val) (realHalfField X e)).address S.names).result=some (wordR e) := by
    change (locate (expectedHalfRow P (oddAxis m) e.val).address S.names).result=some (wordR e)
    have same := actual_old_owner_is_parent_half X e
    change ((Ext).host.network.row e).val=_ at same
    exact (actually_locate_stock_owner P S e.val).trans (congrArg (fun u=>some (name u)) same.symm)
  have obs := actual_half_incidence_program_from_rows m pad S.names (orderedExteriorEdges X)
    (fun e=>side e.val) (realHalfField X) wordR wordC query (actual_physical_half_page_equals_live_key X pad)
  unfold writeExteriorIncidences
  dsimp only
  let observed := real_paid_geometry_comes_from_this_published_header X buf ownHead
  rw [congrArg Meter.result observed]
  refine ⟨obs.1,?_⟩
  have l := (complete_stock_uses_exact_number_of_half_ports P S).1
  have h := obs.2
  rw [l] at h
  have fee := congrArg Meter.steps observed
  change (readPublishedHalfRows X buf).steps=publishedPortDebit m tc tj prec edgew (orderedExteriorEdges X).length at fee
  rw [fee]
  exact Nat.add_le_add_right (Nat.add_le_add_left h _) 4

#print axioms real_old_roster_from_stock
#print axioms true_exterior_incidence_after_named_stock
end
end J6R94ExteriorDebit
