import J6R67CanonicalStopRootFrames

/-! Compile the edge book from the actual R37 lanes used by the root
stop. Its ordinal equivalence describes the order of the already
emitted words; it is not evaluated by the raw reader. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R62Leaf J6R50Leaf J6R52Terminal J6R53TerminalGate
open J6R67CanonicalStop J6R11Blueprint

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000
set_option maxRecDepth 4500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => (exteriorChild G ell X.centre X.sample X.group).host.Edge
local notation "U" => ((exteriorChild G ell X.centre X.sample X.group).host.Row⊕
  (exteriorChild G ell X.centre X.sample X.group).host.Col)
local notation "Fr" => (FramedEdge (rootHalfWidth m) own key prec (pageKeyWidth m+pad))

theorem ordered_exterior_exact_length (edgeCount : (Ext).host.edgeCount=(Ext).edges) :
    (orderedExteriorEdges X).length=(Ext).edges := by
  have h := actual_complete_order_length _ (reviewed_exterior_order X).1 (reviewed_exterior_order X).2
  letI : Fintype E := (Ext).host.finiteEdge
  exact h.trans ((Nat.card_eq_fintype_card (α:=E)).trans edgeCount)

def exteriorOrdinal (edgeCount : (Ext).host.edgeCount=(Ext).edges) :
    Fin (Ext).edges≃E :=
  (finCongr (ordered_exterior_exact_length X edgeCount).symm).trans
    (rosterIndex (orderedExteriorEdges X) (reviewed_exterior_order X).1 (reviewed_exterior_order X).2)

theorem ordinal_lists_actual_exterior (edgeCount : (Ext).host.edgeCount=(Ext).edges) :
    List.ofFn (exteriorOrdinal X edgeCount)=(orderedExteriorEdges X) := by
  apply List.ext_getElem
  · rw [List.length_ofFn,ordered_exterior_exact_length X edgeCount]
  · intro j hj hj'
    rw [List.getElem_ofFn]
    simp only [exteriorOrdinal,Equiv.trans_apply]
    rfl

def exteriorEdgeWord (e : E) : Word (rootHalfWidth m) :=
  (expectedHalfRow P (oddAxis m) e.val).address

theorem exterior_edge_words_injective : Function.Injective (exteriorEdgeWord X) :=
  (half_addresses_unique P (oddAxis m)).comp Subtype.val_injective

theorem two_frame_lanes_share_true_edge_word (name : U→Word own) (e : E) :
    (exteriorFrameAt X gate pad name e).left.id.edge=exteriorEdgeWord X e ∧
    (exteriorFrameAt X gate pad name e).right.id.edge=exteriorEdgeWord X e := ⟨rfl,rfl⟩

def trueFrames (name : U→Word own) :
    List (FramedEdge (rootHalfWidth m) own key prec (pageKeyWidth m+pad)) :=
  (orderedExteriorEdges X).map (exteriorFrameAt X gate pad name)

theorem actual_root_edge_book (name : U→Word own) (edgeCount : (Ext).host.edgeCount=(Ext).edges) :
    frameKeys (trueFrames X gate pad name)=
      ⟨List.ofFn (exteriorEdgeWord X∘exteriorOrdinal X edgeCount),
        3+((trueFrames X gate pad name).map
          (fun x=>3*rootHalfWidth m+5+J6R49SourceLayout.framedIncidenceFee x)).sum⟩ := by
  rw [frame_keys_exact]
  congr 1
  unfold trueFrames
  rw [List.map_map,←ordinal_lists_actual_exterior X edgeCount,List.map_ofFn]
  rfl

def prepareRootBook (name : U→Word own) (owners : PaidIncidentNames X name)
    (lanes : BootLaneTape X gate pad) :
    Meter (Option (List (FramedEdge (rootHalfWidth m) own key prec (pageKeyWidth m+pad)) ×
      List (Word (rootHalfWidth m)))) :=
  let fs := assembleTrueExteriorFrames X gate pad name owners lanes
  match fs.result with
  | none=>⟨none,fs.steps+3⟩
  | some frame=>
    let b := frameKeys frame
    ⟨some (frame,b.result),fs.steps+b.steps+4⟩

theorem prepare_root_book_is_literal_and_paid (name : U→Word own)
    (owners : PaidIncidentNames X name) (lanes : BootLaneTape X gate pad)
    (edgeCount : (Ext).host.edgeCount=(Ext).edges) :
    let fs := trueFrames X gate pad name
    prepareRootBook X gate pad name owners lanes=
      ⟨some (fs,List.ofFn (exteriorEdgeWord X∘exteriorOrdinal X edgeCount)),
        owners.emitted.steps+lanes.run.steps+(Ext).edges*(3*own+8)+
          14+(fs.map (fun x=>3*rootHalfWidth m+5+J6R49SourceLayout.framedIncidenceFee x)).sum⟩ := by
  unfold prepareRootBook
  dsimp only
  rw [paid_mounted_root_frames_exact,ordered_exterior_exact_length X edgeCount]
  dsimp only
  change (⟨some (trueFrames X gate pad name,(frameKeys (trueFrames X gate pad name)).result),
    (owners.emitted.steps+lanes.run.steps+(Ext).edges*(3*own+8)+7)+
      (frameKeys (trueFrames X gate pad name)).steps+4⟩ :
    Meter (Option (List Fr × List (Word (rootHalfWidth m)))))=_
  rw [actual_root_edge_book X gate pad name edgeCount]
  dsimp only
  congr 1
  omega

#print axioms ordered_exterior_exact_length
#print axioms ordinal_lists_actual_exterior
#print axioms exterior_edge_words_injective
#print axioms two_frame_lanes_share_true_edge_word
#print axioms actual_root_edge_book
#print axioms prepare_root_book_is_literal_and_paid
end
end J6R68CanonicalRootWriter

