import J6R62LeafPrepBounds

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 42000000
set_option maxRecDepth 5000

/-! Full finite term with syntactic word widths and actual row/atlas
cardinalities. The packet tariff still reads the exact fetched ancestor
envelope, not an unproven uniform estimate on all old records. -/
namespace J6R62Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
open J6R48Leaf J6R57Public

def observedMax {A : Type*} (value : A → ℕ) (rows : List A) : ℕ :=
  rows.foldr (fun r n=>max (value r) n) 0

theorem current_record_le_observedMax {A : Type*} (value : A → ℕ) (rows : List A) (r : A)
    (used : r∈rows) : value r≤observedMax value rows := by
  induction rows with
  | nil => simp at used
  | cons x xs ih =>
    rcases List.mem_cons.mp used with h|h
    · rw [h]; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

def observedFrameWidth {w own key prec page : ℕ} (rows : List (FramedEdge w own key prec page)) : ℕ :=
  observedMax (fun x=>max x.left.body.length x.right.body.length) rows

theorem frame_width_is_observed {w own key prec page : ℕ} (rows : List (FramedEdge w own key prec page)) :
    FramesFit rows (observedFrameWidth rows) := by
  intro x h
  have hx := current_record_le_observedMax (fun r : FramedEdge w own key prec page=>
    max r.left.body.length r.right.body.length) rows x h
  exact ⟨(le_max_left _ _).trans hx,(le_max_right _ _).trans hx⟩

def observedGateWidth {ow w key prec page : ℕ} (rows : RawRoster ow w key prec page) : ℕ :=
  observedMax (fun x=>match x.payload.gateCode with | none=>0 | some g=>max (gatePorts g) (gateSigns g)) rows

theorem gate_width_is_observed {ow w key prec page : ℕ} (rows : RawRoster ow w key prec page) :
    ∀ row∈rows,∀ g,row.payload.gateCode=some g → GateFit (observedGateWidth rows) g := by
  intro row used g has
  have h := current_record_le_observedMax
    (fun x : RefRow ow (OwnerData w key prec page)=>
      match x.payload.gateCode with | none=>0 | some u=>max (gatePorts u) (gateSigns u)) rows row used
  dsimp only at h
  rw [has] at h
  exact ⟨(le_max_left _ _).trans h,(le_max_right _ _).trans h⟩

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (input : Meter (OwnerTerminalInput X p w Y))
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))

def ownerCensusFee (U d : ℕ) : ℕ :=
  let E := (p.ticket w).child.edges
  let Prev := Nat.card ((p.ticket w).parent.host.Row⊕(p.ticket w).parent.host.Col)
  let O := Nat.card (p.ticket w).child.host.Row
  let W := Y.birth.port
  let own := Y.site.ownerWidth
  let page := pageKeyWidth m+pad
  let oldWidth := pageKeyWidth m+J6Mesh.a m
  bookCap W own key prec page E U+(3+(3*own+77)*Prev+(3*own+1)*O)+
    (3+O*(oldOwnerCap oldWidth W own key prec page E U E d Prev+7))+5

def atlasCensusFee (U : ℕ) : ℕ :=
  let E := (p.ticket w).child.edges
  let W := Y.birth.port
  let own := Y.site.ownerWidth
  let page := pageKeyWidth m+pad
  let N := Y.birth.rows.length
  (3+(3*page+7)*N)+bookCap W own key prec page E U+
    (3+N*(freshPageCap W key page E U+7))+7

def sizedCanonicalLeafFee (older : List (ReadCmd key (pageKeyWidth m+pad))) (U d : ℕ) : ℕ :=
  let F := T.frame (Path.step p w).reached
  let J := older++(trueFreshPages Y).map (freshWord Y)
  let E := (p.ticket w).child.edges
  let e := 4*Nat.clog 2 s
  let pr := (p.ticket w).child.prec
  input.steps+ownerCensusFee X p w Y U d+atlasCensusFee X p w Y U+
    (4*Nat.card (p.ticket w).child.host.Row+3)+(4*E+2)+
    rawLeafCap e ell pr E (vertexCount (p.ticket w).child.host) (cmdBill B e pr E J) F.hp+15

theorem actual_terminal_cap_has_source_sizes
    (older : List (ReadCmd key (pageKeyWidth m+pad)))
    (compiled : (oldCompiler X p w Y input.result).result=some older)
    (U d : ℕ) (frames : FramesFit input.result.saved.rows U)
    (gates : ∀ row∈input.result.roster.raw, ∀ g,row.payload.gateCode=some g → GateFit d g) :
    canonicalLeafFee X p w Y input (T.frame (Path.step p w).reached) B older≤
      sizedCanonicalLeafFee X p w Y input B older U d := by
  let F := T.frame (Path.step p w).reached
  let J := older++(trueFreshPages Y).map (freshWord Y)
  obtain ⟨O,V,_,width,_⟩ := actual_terminal_census_and_native_width X p w Y input.result older compiled
  have setup := actual_canonical_prep_width_bounds X p w Y input.result U d frames gates
  have old : measuredOwnerPrep X p w Y input.result≤ownerCensusFee X p w Y U d := setup.1
  have fresh : measuredAtlasPrep X p w Y input.result≤atlasCensusFee X p w Y U := setup.2
  change F.words.length=4*Nat.clog 2 s at width
  change J.length=vertexCount (p.ticket w).child.host at V
  change input.steps+measuredOwnerPrep X p w Y input.result+measuredAtlasPrep X p w Y input.result+
    (4*older.length+3)+(4*(p.ticket w).child.edges+2)+
    rawLeafCap F.words.length ell (p.ticket w).child.prec (p.ticket w).child.edges J.length
      (cmdBill B F.words.length (p.ticket w).child.prec (p.ticket w).child.edges J) F.hp+15≤_
  unfold sizedCanonicalLeafFee
  dsimp only
  rw [O,V,width]
  gcongr

theorem actual_terminal_with_source_sizes
    (older : List (ReadCmd key (pageKeyWidth m+pad)))
    (compiled : (oldCompiler X p w Y input.result).result=some older)
    (format : ∀ cmd∈older++(trueFreshPages Y).map (freshWord Y),
      ReadFormat B (p.ticket w).child.edges cmd)
    (U d : ℕ) (frames : FramesFit input.result.saved.rows U)
    (gates : ∀ row∈input.result.roster.raw, ∀ g,row.payload.gateCode=some g → GateFit d g) :
    (executeOwnerTerminal X p w Y input (T.frame (Path.step p w).reached) B).steps≤
      sizedCanonicalLeafFee X p w Y input B older U d :=
  (exact_owner_terminal_finite_fee X p w Y input (T.frame (Path.step p w).reached) B older compiled format).trans
    (actual_terminal_cap_has_source_sizes X p w Y input B older compiled U d frames gates)

#print axioms actual_terminal_cap_has_source_sizes
#print axioms actual_terminal_with_source_sizes
#print axioms frame_width_is_observed
#print axioms gate_width_is_observed
end
end J6R62Leaf
