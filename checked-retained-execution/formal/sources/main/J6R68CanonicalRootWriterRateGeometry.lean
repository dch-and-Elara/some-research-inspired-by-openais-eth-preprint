import J6R68CanonicalRootWriterRateRow
import J6R68CanonicalRootWriterWhole
import J6R58BootScopeMount

/-! Specialize the row/build cap to the native root tape: the exact
Gate, true two-body frames and complete owner census determine the sizes.
No bound on the cost of a writer callback is supplied. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6ActiveRun J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R27OriginalGate
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R53OldOwnerRoot J6R50Leaf J6R62Leaf
open J6R67CanonicalStop J6R49SourceLayout J6R24MeteredRecursion J6R58BootScope

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15500000
set_option maxRecDepth 4900
set_option Elab.async false

theorem encoded_gate_operand_shape {A : Type} {n D : ℕ}
    (nfit : n≤D) (port : Fin n→A) (G : Gate n) :
    GateFit D (encodeGate port G) := by
  cases G <;> simp [GateFit,gatePorts,gateSigns,encodeGate,nfit]

def rootBodyWidth (m : ℕ) : ℕ := max (rootHalfWidth m) (2+a m)

def rootBookAfterInputs (m own key prec page E : ℕ) : ℕ :=
  E*(3*own+8)+11+bookCap (rootHalfWidth m) own key prec page E (rootBodyWidth m)

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => (exteriorChild G ell X.centre X.sample X.group).edges
local notation "U" => ((exteriorChild G ell X.centre X.sample X.group).host.Row ⊕ (exteriorChild G ell X.centre X.sample X.group).host.Col)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Raw" => (RawRoster own (SuffixWordWidth m) key prec Pg)

theorem physical_frames_use_printed_payload_widths
    (name : U→Word own) : FramesFit (trueFrames X gate pad name) (rootBodyWidth m) := by
  intro row mem
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp mem
  let F := physicalSeatField (rootChart plant) (oddAxis m) (residentPageKey m) (edge e.val)
  have l : (exteriorFrameAt X gate pad name e).left.body.length=rootHalfWidth m := by
    change (false::(F.page.bits++F.slot.bits)).length=_
    simp only [List.length_cons,List.length_append,F.page.size,F.slot.size,rootHalfWidth]
    omega
  have r : (exteriorFrameAt X gate pad name e).right.body.length=2+a m := by
    change (true::side e.val::F.slot.bits).length=_
    simp only [List.length_cons,F.slot.size]
    omega
  exact ⟨l.le.trans (Nat.le_max_left _ _),r.le.trans (Nat.le_max_right _ _)⟩

theorem physical_roster_gate_fits_from_original_arity
    (name : U→Word own) (owners : ExteriorRoster X gate pad name)
    (D : ℕ) (fit : ∀ u,plant.degree u≤D) :
    ∀ row∈owners.raw,∀ g,row.payload.gateCode=some g → GateFit (max D 2) g := by
  intro row used g got
  rw [owners.exactRows] at used
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp used
  cases v with
  | inl u =>
    let D0 := J6R53OldOwnerRoot.rootLocalGate plant u.val
    let op := encodeGate (rootOperand plant u.val∘D0.port) D0.gate
    have eq : op=g := Option.some.inj got
    rw [←eq]
    exact encoded_gate_operand_shape (original_root_local_gate_fits D fit u.val)
      (rootOperand plant u.val∘D0.port) D0.gate
  | inr k => contradiction

theorem physical_root_book_fee_from_word_widths
    (name : U→Word own) (incident : PaidIncidentNames X name)
    (lanes : BootLaneTape X gate pad) (edgeCount : (Ext).host.edgeCount=E) :
    (prepareRootBook X gate pad name incident lanes).steps≤
      incident.emitted.steps+lanes.run.steps+rootBookAfterInputs m own key prec Pg E := by
  let frames := trueFrames X gate pad name
  have edgeSize : frames.length=E := by
    unfold frames trueFrames
    rw [List.length_map,ordered_exterior_exact_length X edgeCount]
  have book := exact_book_cap frames (physical_frames_use_printed_payload_widths X gate pad name)
  rw [edgeSize] at book
  rw [prepare_root_book_is_literal_and_paid X gate pad name incident lanes edgeCount]
  unfold rootBookAfterInputs actual_frame_book_bill at *
  dsimp only [frames] at book
  dsimp only
  omega

theorem physical_root_command_sum_from_edge_and_vertex_counts
    (name : U→Word own) (owners : ExteriorRoster X gate pad name)
    (edgeCount : (Ext).host.edgeCount=E)
    (width D : ℕ) (arity : ∀ u,plant.degree u≤D) :
    let fs := trueFrames X gate pad name
    let bk := frameKeys fs
    (owners.raw.map (fun row=>(writeRootOwner width bk.result fs row).steps+7)).sum≤
      Nat.card U*rootOwnerRowCap (SuffixWordWidth m) (rootHalfWidth m) own key prec Pg E
        (rootBodyWidth m) width (max D 2) := by
  let fs := trueFrames X gate pad name
  let bk := frameKeys fs
  have e : fs.length=E := by
    unfold fs trueFrames
    rw [List.length_map,ordered_exterior_exact_length X edgeCount]
  have b : bk.result.length=E := by
    unfold bk
    rw [frame_keys_exact]
    dsimp only
    rw [List.length_map,e]
  have n : owners.raw.length=Nat.card U := by
    rw [owners.exactRows,List.length_map]
    exact actual_complete_order_length owners.order owners.unique owners.complete
  have all := root_owner_roster_cost_by_actual_length width (max D 2) bk.result b.le
    fs e.le (physical_frames_use_printed_payload_widths X gate pad name) owners.raw
    (physical_roster_gate_fits_from_original_arity X gate pad name owners D arity)
  rw [n] at all
  exact all

#print axioms encoded_gate_operand_shape
#print axioms physical_frames_use_printed_payload_widths
#print axioms physical_roster_gate_fits_from_original_arity
#print axioms physical_root_book_fee_from_word_widths
#print axioms physical_root_command_sum_from_edge_and_vertex_counts
end
end J6R68CanonicalRootWriter
