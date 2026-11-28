import J6R94ExteriorDebitInputBytes
/-! The complete next-layout target file comes from (i) all old
owner headers including isolated factors and (ii) every Page
of the very same already installed exterior atlas. The incidence
file uses the separately priced reader of the same published head. -/
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
set_option maxHeartbeats 5500000
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
local instance exteriorInputEdge : Fintype Edge := (Ext).host.finiteEdge

variable {name : SourceVertex P→Word own}
variable (S : RootLayoutStock P name)

variable (buf : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (live : IsLive (X.seed pad) buf)
variable (ownHead : OwnsHeader X.header.result buf)

variable (rank a₀ : ℕ) (fit : Fintype.card ((exteriorChild G ell X.centre X.sample X.group).host.Edge)<2^rank)

def exteriorFormat : Format Edge R C (Fin a₀→Fin 64) :=
  childFormat (Ext).host.network rank fit (orderedExteriorEdges X) (reviewed_exterior_order X).1
    (reviewed_exterior_order X).2 (oldWordAt (name:=name) X) (bootPageKey X pad)
    (S.nameInj.comp Subtype.val_injective) (boot_page_key_injective X pad)

def printedExteriorFull64 : Full64Input (Ext).host.network a₀ :=
  let A := stage_owner_order_exact X S.order S.nodup S.complete
  ⟨exteriorFormat X pad S rank a₀ fit,rfl,rfl,rfl,stageOwnerOrder X S.order,A.1,A.2⟩

include live in
theorem real_exterior_targets_match_the_same_format :
    (writeExteriorTargets X pad S buf).result=
      (printedExteriorFull64 X pad S rank a₀ fit).order.map
        (printedExteriorFull64 X pad S rank a₀ fit).format.target := by
  have p := (read_same_live_exterior_page_words X pad buf live).1
  have r := (real_old_roster_from_stock X S).1
  unfold writeExteriorTargets currentPageKeys
  dsimp only
  rw [p,r]
  exact (typed_target_tape (a:=a₀) (Ext).host.network rank fit (orderedExteriorEdges X)
    (reviewed_exterior_order X).1 (reviewed_exterior_order X).2 (oldWordAt (name:=name) X)
    (bootPageKey X pad) (S.nameInj.comp Subtype.val_injective) (boot_page_key_injective X pad)
    (stageOldOrder X S.order) (stagePageOrder X)).1

def exteriorIngress : Ingress (printedExteriorFull64 X pad S rank a₀ fit) :=
  let cmds := writeExteriorTargets X pad S buf
  let rows := writeExteriorIncidences X pad S buf
  { paid := ⟨(cmds.result,rows.result.getD []),cmds.steps+rows.steps+4⟩
    commands := real_exterior_targets_match_the_same_format X pad S buf live rank a₀ fit
    incidences := by
      change (writeExteriorIncidences X pad S buf).result.getD []=
        (printedExteriorFull64 X pad S rank a₀ fit).raw
      rw [(true_exterior_incidence_after_named_stock X pad S buf ownHead).1]
      dsimp only [Option.getD,printedExteriorFull64,exteriorFormat,Full64Input.raw,childFormat]
      apply List.map_congr_left
      intro e _
      exact Prod.ext
        (congrArg Word.bits (valued_word (oldWordAt (name:=name) X ((Ext).host.network.row e)))).symm
        (congrArg Word.bits (valued_word (bootPageKey X pad ((Ext).host.network.col e)))).symm }

theorem exact_exterior_ingress_bill :
    (exteriorIngress X pad S buf live ownHead rank a₀ fit).paid.steps=
      (writeExteriorTargets X pad S buf).steps+(writeExteriorIncidences X pad S buf).steps+4 := rfl

#print axioms real_old_roster_from_stock
#print axioms true_exterior_incidence_after_named_stock
#print axioms printedExteriorFull64
#print axioms real_exterior_targets_match_the_same_format
#print axioms exteriorIngress
#print axioms exact_exterior_ingress_bill
end
end J6R94ExteriorDebit
