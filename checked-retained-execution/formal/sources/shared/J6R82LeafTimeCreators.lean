import J6R66LeafTariffReadCmd
import J6R66LeafTariffCounts
import J6R58LeafScaleArithmetic

/-! Obtain the actual creator's census along the one live path.
Exterior and recursively issued creators may differ in precision but
both use the same source-size bound. No source owner's value is used
as a fee premise. -/
namespace J6R82LeafTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 J6R15ModeCost J6R21Ancestor
open J6R18ChildWrite J6R20Ancestor J6R22Active J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R34RootAtlas
open J6R12Blueprint J6R11Blueprint J6ActiveRun J6ActiveSchedule J1PPrinted
open J6R48Leaf J6R50Leaf J6R62Leaf J6R65LeafRate J6R66LeafTariff
open J6R26DescriptorTree J6R34ChildPath J6R49SourceLayout J6R32ChildResidentTransfer
open P11FullPacking J6R10Repack J6R51Online J6R50SourceProducer J6R48DFS
open J6Mesh J6OrientedHost J6R27OriginalGate J6R24LegalLayout J6R26StablePreparedRoot
open J6R35RootOrigins J6R31RootResidentTables J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 35000000
set_option maxRecDepth 5500
set_option Elab.async false

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Rec" => (Stored key prec tw bw (PagedEnvelope f ell prec page))

def regulator (s C : ℕ) : ℕ := 321*C*s^2
def leafH (s : ℕ) : ℕ := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)

structure CreatedSourceDimensions (s C : ℕ) (r : Rec) (d : pageFields r) : Prop where
  axis : ∃ dep,r.payload.shape.a=stepA (Nat.clog 2 s) dep
  pMax : r.payload.shape.p≤regulator s C
  rows : d.rows.length≤2^r.payload.shape.a
  cols : d.cols.length≤2^r.payload.shape.a
  modes : d.modes.length≤3*(C*s)*(regulator s C)
  pages : r.payload.pages.length≤3*(C*s)

structure CurrentPacketReceipt (B : Bank) (addr : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
    (s C e p edges depth : ℕ) (wires : List WireRead) where
  record : Rec
  data : pageFields record
  outer : (locate addr B.records).result=some record
  inner : (locate pg record.payload.pages).result=some data
  geometry : CreatedSourceDimensions s C record data
  rate : readCmdFee B e p edges (.packet addr pg depth wires)≤
    2^(6*leafH s)*actualPacketPrefactor B record data p depth wires

noncomputable section
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c target : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}

theorem real_native_creator_for_this_address
    (par : Path sel r c) (slot : (Plan sel).Slot c)
    (I : OccurrenceInput T (par.ticket slot) key prec tw bw page)
    (k : PageAt T (par.ticket slot)) (path : Path sel r target)
    (born : Births T key prec tw bw page)
    (used : OnPath born (compileOccurrence I).job path)
    (original : Bank→Prop) (B : Bank) (openedHere : opened born original path B)
    (start : r.prec≤161*C*s^2) (e p edges dep : ℕ) (wires : List WireRead) :
    Nonempty (CurrentPacketReceipt B (compileOccurrence I).job.identifier (occurrencePageWord I k)
      s C e p edges dep wires) := by
  let job := (compileOccurrence I).job
  let R := job.immutable.payload
  have here : IsLive job B := ancestor_paged_live born job path used B openedHere
  obtain ⟨fld,hit,axis,pp,rows,cols,modes⟩ :=
    actual_ancestor_page_has_printed_dimensions par slot I k
  obtain ⟨chosen,hit',fee⟩ :=
    actual_reached_ancestor_reader_geometric par slot I k path born used original B openedHere
      start (e:=e) (p:=p) (edges:=edges) dep wires
  have eq : fld=chosen := Option.some.inj (hit.symm.trans hit')
  subst chosen
  have pMax : R.payload.shape.p≤regulator s C := by
    calc
      _≤r.prec+160*C*s^2 := pp
      _≤161*C*s^2+160*C*s^2 := Nat.add_le_add_right start _
      _=_ := by unfold regulator; ring
  have pageMax := actual_native_inner_atlas_capacity par slot I
  refine ⟨⟨R,fld,here.2,hit,⟨⟨c.depth,axis⟩,pMax,rows,cols,
    modes.trans (Nat.mul_le_mul_left _ pMax),pageMax⟩,?_⟩⟩
  exact fee

variable {V : Type} [Fintype V] {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (constantRootWord m)}
variable {q ro co de edgew tc tj : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)

theorem true_exterior_creator_for_this_address
    (hn : native≤m) (sourceSize : s=physicalSize m native)
    (baseFit : base≤C*s) (pad : ℕ) (k : CanonicalPage m)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (live : IsLive (X.seed pad) B)
    (e p edges dep : ℕ) (wires : List WireRead) (bounds : RootBounds s C f) :
    Nonempty (CurrentPacketReceipt B (X.seed pad).identifier
      (widened pad (residentPageKey m k)).result s C e p edges dep wires) := by
  subst s
  let s := physicalSize m native
  let job := X.seed pad
  let R := job.immutable.payload
  let F : pageFields R := X.chosenFields k
  have sameAxis : R.payload.shape.a=stepA (Nat.clog 2 s) 0 :=
    (same_printed_source_mesh m native hn).symm
  have p₀ : J6SourcePrecision.printed m base≤161*C*s^2 :=
    printed_exterior_register_size m native base C hn bounds.constPos baseFit
  have pMax : R.payload.shape.p≤regulator s C := by
    change J6SourcePrecision.printed m base≤321*C*s^2
    exact p₀.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))
  have actual := printed_exterior_page_dimensions X k
  have mesh := actual_mesh_M_at_most_twice_source m native hn
  have groupM : 2*s≤3*(C*s) := by
    have h : s≤C*s := Nat.le_mul_of_pos_left _ bounds.constPos
    omega
  have mMax : F.modes.length≤3*(C*s)*(regulator s C) := by
    refine actual.2.2.trans ?_
    apply Nat.mul_le_mul (mesh.trans groupM)
    exact (Nat.sub_le _ _).trans pMax
  have pages : R.payload.pages.length≤3*(C*s) :=
    (Nat.le_mul_of_pos_right _ (show 0<L m by unfold L; positivity)).trans
      ((printed_exterior_atlas_count X pad).2.le.trans (mesh.trans groupM))
  have fee := actual_exterior_reader_geometric X hn bounds.constPos bounds.constSmall baseFit
    (physical_exterior_source_lambda_large m native hn) pad k B live (p:=p) (e:=e)
    (edges:=edges) dep wires
  exact ⟨⟨R,F,live.2,true_seed_payload_page X pad k,
    ⟨⟨0,sameAxis⟩,pMax,actual.1,actual.2.1,mMax,pages⟩,fee⟩⟩

#print axioms real_native_creator_for_this_address
#print axioms true_exterior_creator_for_this_address
end
end J6R82LeafTime
