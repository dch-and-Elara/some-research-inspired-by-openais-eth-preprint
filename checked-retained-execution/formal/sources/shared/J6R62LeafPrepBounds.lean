import J6R62LeafOwnerPrep
import J6R62LeafCensus

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 33000000
set_option maxRecDepth 4200

/-! Owner and fresh atlas preparation have finite bounds in actual
table counts and syntactic word bounds. Unlike the old LeafChart
entry-cost assumption, these bounds price the very operations run. -/
namespace J6R62Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
open J6R48Leaf J6R57Public

def ownerDataCap (w key prec page d : ℕ) :=
  originFee key prec page true+d*(3*w+8)+20

def bookCap (W own key prec page E U : ℕ) :=
  3+E*(3*W+5+jacketCap W own key prec page U)

def oldOwnerCap (w W own key prec page E U b d roster : ℕ) :=
  locateFee own roster+ownerDataCap w key prec page d+
    (keptPageCap W own key prec page E U+savedGateCap w W own E U b d)+12

def freshPageCap (W key page E U : ℕ) :=
  freshScanCap W page E U+emitCap W E U+(3*key+1)+(3*page+1)+7

theorem exact_book_cap {W own key prec page U : ℕ}
    (fs : List (FramedEdge W own key prec page)) (fit : FramesFit fs U) :
    actual_frame_book_bill fs≤bookCap W own key prec page fs.length U := by
  unfold actual_frame_book_bill bookCap
  apply Nat.add_le_add_left
  apply sum_map_cap
  intro x hx
  obtain ⟨l,r⟩ := fit x hx
  exact Nat.add_le_add_left (frame_fee_under_real_word_width x l r) _

theorem actual_fresh_page_compile_cap {W own key prec page E U : ℕ}
    (id : Word key) (book : List (Word W)) (nb : book.length≤E)
    (fs : List (FramedEdge W own key prec page)) (nf : fs.length≤E)
    (fit : FramesFit fs U) (pg : Word page) :
    (compileFreshOne id book fs pg).steps≤freshPageCap W key page E U := by
  let calls := scanFresh pg fs
  obtain ⟨n,forms,fee⟩ := fresh_scan_bounded fs fit pg
  have nc : calls.result.length≤E := n.trans nf
  have hcall : calls.steps≤freshScanCap W page E U :=
    fee.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ nf) _)
  have ha := wire_emission_fee book calls.result forms
  have hb : (emitWires book calls.result).steps≤emitCap W E U := by
    apply ha.trans
    unfold emitCap
    exact Nat.add_le_add_left
      (Nat.mul_le_mul nc (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ nb) _) _)) _
  change calls.steps+(emitWires book calls.result).steps+(copyFixed id).steps+
    (copyFixed pg).steps+7≤_
  rw [copy_fixed_exact,copy_fixed_exact]
  unfold freshPageCap
  dsimp only
  omega

theorem actual_gate_roster_payload_cap {w key prec page d : ℕ} (v : OwnerData w key prec page)
    (gateFit : ∀ g,v.gateCode=some g→GateFit d g) :
    ownerDataFee v≤ownerDataCap w key prec page d := by
  have ho := origin_fee_upper key prec page v.origin.pageKey.isSome
  unfold ownerDataFee ownerDataCap
  cases hx : v.gateCode with
  | none => simp only [optGateFee]; omega
  | some code =>
    obtain ⟨po,si⟩ := gateFit code hx
    have cap : d*(3*w+8)=(3*w+5)*d+3*d := by ring
    rw [cap]
    cases code <;> simp only [gatePorts,gateSigns,optGateFee,gateCopyFee] at *
    all_goals
      have pr := Nat.mul_le_mul_left (3*w+5) po
      omega

theorem locate_returns_actual_row {own : ℕ} {D : Type*} (k : Word own) (rows : List (RefRow own D)) (d : D)
    (hit : (locate k rows).result=some d) : ∃ row∈rows,row.payload=d := by
  induction rows with
  | nil => simp [locate] at hit
  | cons x xs ih =>
    simp only [locate] at hit
    split at hit
    · exact ⟨x,List.mem_cons_self,Option.some.inj hit⟩
    · obtain ⟨r,mem,h⟩ := ih hit
      exact ⟨r,List.mem_cons_of_mem _ mem,h⟩

theorem finite_owner_roster_compile_cap {W w own key prec page E U b d : ℕ}
    (book : List (Word W)) (nb : book.length≤E)
    (fs : List (FramedEdge W own key prec page)) (nf : fs.length≤E)
    (fit : FramesFit fs U) (raw : RawRoster own w key prec page) (id : Word own)
    (gateFit : ∀ row∈raw, ∀ g,row.payload.gateCode=some g→GateFit d g) :
    (compileByRoster b book fs raw id).steps≤oldOwnerCap w W own key prec page E U b d raw.length := by
  have look := locate_bound id raw
  cases hit : (locate id raw).result with
  | none =>
    dsimp only [compileByRoster,paidOwnerLookup]
    rw [hit]
    dsimp only
    unfold oldOwnerCap
    omega
  | some value =>
    obtain ⟨row,mem,rfl⟩ := locate_returns_actual_row id raw _ hit
    have cost := actual_gate_roster_payload_cap row.payload (gateFit row mem)
    have chosen : (compileByOwnerData b book fs id row.payload).steps≤
        keptPageCap W own key prec page E U+savedGateCap w W own E U b d+4 := by
      unfold compileByOwnerData
      cases h : row.payload.gateCode with
      | none =>
        have alone := same_owner_page_compilation_fee fs fit nf book nb id row.payload.origin
        dsimp only
        omega
      | some gate =>
        have alone := same_owner_gate_compilation_fee fs fit nf book nb id b d gate (gateFit row mem gate h)
        dsimp only
        omega
    unfold compileByRoster
    dsimp only
    rw [paid_owner_lookup_exact raw id row.payload hit]
    unfold oldOwnerCap
    dsimp only
    omega

#print axioms exact_book_cap
#print axioms actual_fresh_page_compile_cap
#print axioms actual_gate_roster_payload_cap
#print axioms finite_owner_roster_compile_cap

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

theorem actual_canonical_prep_width_bounds
    (A : OwnerTerminalInput X p w Y) (U d : ℕ)
    (frameFit : FramesFit A.saved.rows U)
    (gateFit : ∀ row∈A.roster.raw, ∀ g,row.payload.gateCode=some g → GateFit d g) :
    let E := (p.ticket w).child.edges
    let Prev := Nat.card ((p.ticket w).parent.host.Row⊕(p.ticket w).parent.host.Col)
    let O := Nat.card (p.ticket w).child.host.Row
    let N := Y.birth.rows.length
    let W := Y.birth.port
    let own := Y.site.ownerWidth
    let page := pageKeyWidth m+pad
    let oldWidth := pageKeyWidth m+J6Mesh.a m
    let book := bookCap W own key prec page E U
    measuredOwnerPrep X p w Y A≤
      book+(3+(3*own+77)*Prev+(3*own+1)*O)+
        (3+O*(oldOwnerCap oldWidth W own key prec page E U E d Prev+7))+5 ∧
    measuredAtlasPrep X p w Y A≤
      (3+(3*page+7)*N)+book+(3+N*(freshPageCap W key page E U+7))+7 := by
  let E := (p.ticket w).child.edges
  let W := Y.birth.port
  let own := Y.site.ownerWidth
  let pg := pageKeyWidth m+pad
  let oldWidth := pageKeyWidth m+J6Mesh.a m
  let Prev := Nat.card ((p.ticket w).parent.host.Row⊕(p.ticket w).parent.host.Col)
  let O := Nat.card (p.ticket w).child.host.Row
  let chosen := (selectOwnerKeys (word (p.ticket w).groupAt.val) A.headers.raw).result
  let book := cachedBook Y A.saved
  let pageCaps := freshPageCap W key pg E U
  let ownerCaps := oldOwnerCap oldWidth W own key prec pg E U E d Prev
  have counts := canonical_terminal_table_censuses X p w Y A
  have framesN : A.saved.rows.length=E := counts.1
  have bookN : book.result.length=E := by
    unfold book cachedBook
    rw [frame_keys_exact]
    change (_ : List (Word W)).length=E
    rw [List.length_map]
    exact framesN
  have headersN : A.headers.raw.length=Prev := counts.2.1
  have rosterN : A.roster.raw.length=Prev := counts.2.2.1
  have atlasN : (trueFreshPages Y).length=Y.birth.rows.length := counts.2.2.2
  have selectedN : chosen.length=O := actual_selected_owner_count X p w Y A
  have bc : actual_frame_book_bill A.saved.rows≤bookCap W own key prec pg E U := by
    have h := exact_book_cap A.saved.rows frameFit
    rw [framesN] at h
    exact h
  have oc (id : Word own) :
      (compileByRoster E book.result A.saved.rows A.roster.raw id).steps≤ownerCaps := by
    have h := finite_owner_roster_compile_cap book.result bookN.le A.saved.rows framesN.le frameFit
      A.roster.raw id (b:=E) gateFit
    rw [rosterN] at h
    exact h
  have pc (k : PageAt T (p.ticket w)) : freshItemFee Y A.saved k≤pageCaps := by
    have h := actual_fresh_page_compile_cap Y.birth.job.identifier book.result bookN.le
      A.saved.rows framesN.le frameFit (occurrencePageWord Y.input k)
    exact (compile_cached_fresh_one Y A.saved k).2.symm.trans_le h
  have oldSum := sum_map_cap chosen (fun id=>(compileByRoster E book.result A.saved.rows A.roster.raw id).steps+7)
    (ownerCaps+7) (fun id _=>Nat.add_le_add_right (oc id) _)
  have newSum := sum_map_cap (trueFreshPages Y) (fun k=>freshItemFee Y A.saved k+7)
    (pageCaps+7) (fun k _=>Nat.add_le_add_right (pc k) _)
  dsimp only
  constructor
  · change actual_frame_book_bill A.saved.rows+
      (3+(3*own+77)*A.headers.raw.length+(3*own+1)*chosen.length)+
      (3+(chosen.map (fun id=>(compileByRoster E book.result A.saved.rows A.roster.raw id).steps+7)).sum)+5≤
        bookCap W own key prec pg E U+(3+(3*own+77)*Prev+(3*own+1)*O)+
          (3+O*(ownerCaps+7))+5
    rw [headersN,selectedN]
    rw [selectedN] at oldSum
    gcongr
  · change (3+(3*pg+7)*Y.birth.rows.length)+actual_frame_book_bill A.saved.rows+
      (3+((trueFreshPages Y).map (fun k=>freshItemFee Y A.saved k+7)).sum)+7≤
        (3+(3*pg+7)*Y.birth.rows.length)+bookCap W own key prec pg E U+
          (3+Y.birth.rows.length*(pageCaps+7))+7
    rw [atlasN] at newSum
    gcongr

#print axioms actual_canonical_prep_width_bounds
end

end J6R62Leaf
