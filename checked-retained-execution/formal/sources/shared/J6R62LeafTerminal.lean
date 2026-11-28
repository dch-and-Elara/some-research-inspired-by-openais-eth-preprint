import J6R62LeafReader
import J6R57PublicNoChartExactRows
import J6R53TerminalGateWhole
import J6R58LeafScaleNative

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 33000000
set_option maxRecDepth 4100

/-! The same paid owner leaf as in R57, not another evaluator. The
only surviving program fee in the binder is the already-measured input
supplier; the terminal's own work is decomposed at its installed frames,
owners, literal child atlas, and true per-vertex row reader. -/
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
open J6R48Leaf J6R57Public J6R58LeafScale

theorem actual_gather_step_list {A D : Type*} (s : ℕ) (f : A → Meter (Option D)) (xs : List A) :
    (gatherOptions s f xs).steps=3+(xs.map (fun x=>(f x).steps+s+6)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [gatherOptions,List.map_cons,List.sum_cons,ih]
    omega

theorem actual_complete_order_length {A : Type*} (xs : List A) (u : xs.Nodup)
    (all : ∀ x,x∈xs) : xs.length=Nat.card A :=
  (Nat.card_fin _).symm.trans (Nat.card_congr (u.getEquivOfForallMemList xs all))

def actual_frame_book_bill {w own key prec page : ℕ}
    (fs : List (FramedEdge w own key prec page)) : ℕ :=
  3+(fs.map (fun x=>3*w+5+framedIncidenceFee x)).sum

theorem actual_owner_selection_bill {own W w key prec page : ℕ}
    (b : ℕ) (book : Meter (List (Word W))) (frames : List (FramedEdge W own key prec page))
    (roster : RawRoster own w key prec page) (headers : List (OwnerGroup own)) (g : Word 6) :
    let hits := (selectOwnerKeys g headers).result
    (compileSelectedOwners b book frames roster headers g).steps=
      book.steps+(3+(3*own+77)*headers.length+(3*own+1)*hits.length)+
        (3+(hits.map (fun id=>(compileByRoster b book.result frames roster id).steps+7)).sum)+5 := by
  dsimp only [compileSelectedOwners]
  rw [actual_gather_step_list,select_owner_keys_exact]

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

theorem canonical_terminal_table_censuses (A : OwnerTerminalInput X p w Y) :
    A.saved.rows.length=(p.ticket w).child.edges ∧
      A.headers.raw.length=Nat.card ((p.ticket w).parent.host.Row⊕(p.ticket w).parent.host.Col) ∧
      A.roster.raw.length=Nat.card ((p.ticket w).parent.host.Row⊕(p.ticket w).parent.host.Col) ∧
      (trueFreshPages Y).length=Y.birth.rows.length := by
  obtain ⟨frames,headers,roster,h,r⟩ := owner_terminal_tables_are_exact_source_lists X p w Y A
  refine ⟨?_,?_,?_,?_⟩
  · rw [frames,List.length_map,half_order_length]
  · rw [headers,List.length_map]
    exact actual_complete_order_length A.headers.order h.1 h.2
  · rw [roster,List.length_map]
    exact actual_complete_order_length A.roster.order r.1 r.2
  · have got := congrArg List.length (compiled_occurrence_has_full_ordered_keys Y.input).1
    change (readBankKeys Y.birth.rows).result.length=
      ((trueFreshPages Y).map (occurrencePageWord Y.input)).length at got
    rw [read_bank_keys_exact] at got
    exact (by simpa only [List.length_map] using got.symm)

def oldCompiler
    (A : OwnerTerminalInput X p w Y) : Meter (Option (List (ReadCmd key (pageKeyWidth m+pad)))) :=
  compileSelectedOwners (p.ticket w).child.edges (cachedBook Y A.saved) A.saved.rows A.roster.raw A.headers.raw
    (word (p.ticket w).groupAt.val)

def measuredOwnerPrep (A : OwnerTerminalInput X p w Y) : ℕ :=
  let book := cachedBook Y A.saved
  let hits := (selectOwnerKeys (word (p.ticket w).groupAt.val) A.headers.raw).result
  actual_frame_book_bill A.saved.rows+
    (3+(3*Y.site.ownerWidth+77)*A.headers.raw.length+(3*Y.site.ownerWidth+1)*hits.length)+
    (3+(hits.map (fun k=>
      (compileByRoster (p.ticket w).child.edges book.result A.saved.rows A.roster.raw k).steps+7)).sum)+5

def measuredAtlasPrep (A : OwnerTerminalInput X p w Y) : ℕ :=
  (3+(3*(pageKeyWidth m+pad)+7)*Y.birth.rows.length)+actual_frame_book_bill A.saved.rows+
    (3+((trueFreshPages Y).map (fun k=>freshItemFee Y A.saved k+7)).sum)+7

theorem actual_owner_branch_fee (A : OwnerTerminalInput X p w Y) :
    (oldCompiler X p w Y A).steps=measuredOwnerPrep X p w Y A := by
  unfold oldCompiler measuredOwnerPrep
  rw [actual_owner_selection_bill]
  have book := (cached_book_exact Y A.saved).2
  rw [book]
  rfl

theorem actual_atlas_branch_fee (A : OwnerTerminalInput X p w Y) :
    (compileAllFresh Y A.saved).steps=measuredAtlasPrep X p w Y A := by
  have eq := (all_fresh_commands_from_actual_paid_roster Y A.saved).2
  have book := (cached_book_exact Y A.saved).2
  rw [eq,book]
  rfl

variable (input : Meter (OwnerTerminalInput X p w Y))
variable (F : Frame f (p.ticket w).child.prec)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))

def canonicalLeafFee (older : List (ReadCmd key (pageKeyWidth m+pad))) : ℕ :=
  let cmds := older++(trueFreshPages Y).map (freshWord Y)
  input.steps+measuredOwnerPrep X p w Y input.result+measuredAtlasPrep X p w Y input.result+
    (4*older.length+3)+(4*(p.ticket w).child.edges+2)+
    rawLeafCap F.words.length ell (p.ticket w).child.prec (p.ticket w).child.edges cmds.length
      (cmdBill B F.words.length (p.ticket w).child.prec (p.ticket w).child.edges cmds) F.hp+15

/-- Actual positive terminal finite fee (including the owner supplier and
the real child-clock Boolean enumeration). No whole-leaf tariff, no
LoopCharts, and no caller-supplied row interpreter or numeric fee. -/
theorem exact_owner_terminal_finite_fee
    (older : List (ReadCmd key (pageKeyWidth m+pad)))
    (oldSuccess : (oldCompiler X p w Y input.result).result=some older)
    (format : ∀ cmd∈older++(trueFreshPages Y).map (freshWord Y),
      ReadFormat B (p.ticket w).child.edges cmd) :
    (executeOwnerTerminal X p w Y input F B).steps≤canonicalLeafFee X p w Y input F B older := by
  let A := input.result
  let cmds := older++(trueFreshPages Y).map (freshWord Y)
  let old := oldCompiler X p w Y A
  let clock := visitFramesClock A.saved.rows
  have checked := same_row_interpreter_fee X.hf F T.vPositive B clock.result
    (clock_from_actual_frame_has_all_bits Y A.saved) cmds format
  have e : (joinPaidTerminal Y A.saved old F B).steps=
      old.steps+(compileAllFresh Y A.saved).steps+(4*older.length+3)+clock.steps+
        (runRows X.hf F T.vPositive B clock.result cmds).steps+11 :=
    congrArg Meter.steps (measured_joined_terminal_exact Y A.saved old F B older oldSuccess)
  have cfee : clock.steps=4*(p.ticket w).child.edges+2 := by
    unfold clock
    rw [frame_clock_exact,(canonical_terminal_table_censuses X p w Y A).1]
  change input.steps+(joinPaidTerminal Y A.saved old F B).steps+4≤_
  rw [e,show old.steps=_ from actual_owner_branch_fee X p w Y A,actual_atlas_branch_fee X p w Y A,cfee]
  change input.steps+(measuredOwnerPrep X p w Y A+measuredAtlasPrep X p w Y A+
    (4*older.length+3)+(4*(p.ticket w).child.edges+2)+
    (runRows X.hf F T.vPositive B clock.result cmds).steps+11)+4≤
    input.steps+measuredOwnerPrep X p w Y A+measuredAtlasPrep X p w Y A+
    (4*older.length+3)+(4*(p.ticket w).child.edges+2)+
    rawLeafCap F.words.length ell (p.ticket w).child.prec (p.ticket w).child.edges cmds.length
      (cmdBill B F.words.length (p.ticket w).child.prec (p.ticket w).child.edges cmds) F.hp+15
  omega

theorem canonical_terminal_uses_actual_current_atlas (rootPrec :
    (exteriorChild G ell X.centre X.sample X.group).prec≤C*s) :
    let SP := printedParams (f:=f) (ell:=ell) s
    let a := SP.levelBits c.depth
    let pwidth := registerPrecision SP c (p.ticket w).centerAt
    let h := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
    let i := (centerIndex (ticketReady T (p.ticket w)) (p.ticket w).centerAt).val
    let hp := register_positive (ticketReady T (p.ticket w)) (p.ticket w).centerAt
    (trueFreshPages Y).length*2^a≤3*(C*s) ∧
      pwidth≤(exteriorChild G ell X.centre X.sample X.group).prec+160*C*s^2 ∧
      ∀ k,
        let fld := ((chosenAtlas Y.input).page k).fields
        let e := Y.input.fw.length
        let l := fld.rows.length
        let j := fld.cols.length
        let u := fld.modes.length
        l≤2^a ∧ j≤2^a ∧ u≤3*(C*s)*pwidth ∧
        J6R18ChildWrite.packetFee a e ell pwidth i (Y.input.q+1) Y.input.code l j u hp+
          J6R18ChildWrite.packetFramingFee e ell pwidth (Y.input.q+1)≤
        2^(6*h)*(J6R18ChildWrite.packetNonTreeFee a e ell pwidth i (Y.input.q+1) Y.input.code l j u hp+
          J6R18ChildWrite.packetTreeScale e ell pwidth u l Y.input.code (Y.input.q+1) hp+
          J6R18ChildWrite.packetFramingFee e ell pwidth (Y.input.q+1)) := by
  have h := actual_occurrence_compact_chart p w Y.input
  have g := actual_occurrence_packet_geometric_not_promised p w Y.input rootPrec
  have got := congrArg List.length (compiled_occurrence_has_full_ordered_keys Y.input).1
  change (readBankKeys Y.birth.rows).result.length=
    ((trueFreshPages Y).map (occurrencePageWord Y.input)).length at got
  rw [read_bank_keys_exact] at got
  have atLen : (trueFreshPages Y).length=Y.birth.rows.length := by
    simpa only [List.length_map] using got.symm
  dsimp only at h g ⊢
  rw [atLen]
  refine ⟨h.1,h.2.1,?_⟩
  intro k
  have dimensions := h.2.2 k
  exact ⟨dimensions.1,dimensions.2.1,dimensions.2.2,g k⟩

#print axioms canonical_terminal_table_censuses
#print axioms actual_owner_branch_fee
#print axioms actual_atlas_branch_fee
#print axioms exact_owner_terminal_finite_fee
#print axioms canonical_terminal_uses_actual_current_atlas
end
end J6R62Leaf
