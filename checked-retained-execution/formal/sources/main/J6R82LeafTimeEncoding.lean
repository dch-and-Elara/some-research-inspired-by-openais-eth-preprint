import J6R82LeafTimeContext

/-! Same-path stopped-leaf prices. The printed source exponent is unchanged.
The scalar uses actual encoded widths; these are not inferred from mere
value-equivalence of an arbitrary replacement chart. -/
namespace J6R82LeafTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

open J6R30ProducedGateRegistry J6R33GeneratedChildSite J6R15ModeCost
open J6R20Ancestor

section BankCapacity
variable {pg : ℕ}

private theorem successful_bank_lookup_contains_record
    {R : Type} (address : Word key) (rows : List (RefRow key R)) (r : R)
    (hit : (locate address rows).result=some r) :
    ∃ row∈rows,row.payload=r := by
  induction rows with
  | nil => simp [locate] at hit
  | cons x xs ih =>
    rw [locate] at hit
    split at hit
    · exact ⟨x,List.mem_cons_self,Option.some.inj hit⟩
    · obtain ⟨u,h,eq⟩ := ih hit
      exact ⟨u,List.mem_cons_of_mem _ h,eq⟩

/-- Widths used by a real lookup depend on the stored row. The code parameter
    is bounded by the numeric capacity of the carried machine word. -/
theorem storage_widths_supply_actual_encoding
    (B : PageBank f ell key prec tw bw pg) {K : ℕ}
    (width : ∀ row∈B.records,row.payload.payload.shape.w≤K)
    (codeWidth : 2^bw≤K) : ActualEncodingFits B K := by
  intro addr R hit
  obtain ⟨row,existsRow,rfl⟩ := successful_bank_lookup_contains_record addr B.records R hit
  exact ⟨width row existsRow,(val_lt row.payload.context.codeWidth).le.trans codeWidth⟩

private theorem count_width_after_transport
    {u v : ℕ} (h : u=v) {t : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
    (b : J6R33StatefulArithmeticPage.Birth T t key prec tw bw u) :
    let q : J6R33StatefulArithmeticPage.Birth T t key prec tw bw v := h ▸ b
    q.job.immutable.payload.payload.shape.w=b.job.immutable.payload.payload.shape.w := by
  subst v
  rfl

theorem actual_native_count_field_fits_page_word
    {t : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
    (I : OccurrenceInput T t key prec tw bw pg) :
    (compileOccurrence I).job.immutable.payload.payload.shape.w≤pg+1 := by
  let chosen := Classical.choice (occurrence_real_receipt I)
  let issue := padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let birth := issuedBirth I.native.result issue I.words.result I.hOld chosen
  change ((I.width ▸ birth : J6R33StatefulArithmeticPage.Birth T t key prec tw bw pg).job.immutable.payload.payload.shape.w)≤pg+1
  rw [count_width_after_transport X I.width birth]
  change I.q+1≤pg+1
  have width := I.width
  omega

private theorem afterOne_shape_width
    (B : PageBank f ell key prec tw bw pg) (j : PageJob f ell key prec tw bw pg) (K : ℕ)
    (start : ∀ row∈B.records,row.payload.payload.shape.w≤K)
    (here : j.immutable.payload.payload.shape.w≤K) :
    ∀ row∈(afterOne B j).records,row.payload.payload.shape.w≤K := by
  intro row h
  change row∈j.immutable::B.records at h
  rcases List.mem_cons.mp h with eq|rest
  · rw [eq]; exact here
  · exact start row rest

end BankCapacity

def realLookupWidth (q page bw : ℕ) := max q (max (page+1) (2^bw))

theorem real_stack_encoding_from_initial_width
    (initial : Bank) (path : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
    (start : ∀ row∈initial.records,row.payload.payload.shape.w≤realLookupWidth q (pageKeyWidth m+pad) bw) :
    ActualEncodingFits (stackBank (borns M) initial path) (realLookupWidth q (pageKeyWidth m+pad) bw) := by
  let K := realLookupWidth q (pageKeyWidth m+pad) bw
  have countWidth : pageKeyWidth m+pad+1≤K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have codeWidth : 2^bw≤K := (le_max_right _ _).trans (le_max_right _ _)
  have shapes : ∀ row∈(stackBank (borns M) initial path).records,row.payload.payload.shape.w≤K := by
    induction path with
    | root => exact start
    | step par slot ih =>
      apply afterOne_shape_width _ _ K ih
      exact (actual_native_count_field_fits_page_word X (sourceState M par slot).input).trans countWidth
  exact storage_widths_supply_actual_encoding _ shapes codeWidth

theorem real_stack_encoding_from_singleton_mount
    (path : Path sel (exteriorChild G ell X.centre X.sample X.group) c) :
    ActualEncodingFits (stackBank (borns M) (mountFromEmpty (X.seed pad)).result.1 path)
      (realLookupWidth q (pageKeyWidth m+pad) bw) := by
  let empty : Bank := ⟨[],[]⟩
  have ready : JobsReady empty [X.seed pad] := by
    refine ⟨rfl,by simp,?_⟩
    intro j hj row atRow
    have h : row∈([] : List (DirRow key)) := atRow
    exact (List.not_mem_nil h).elim
  have mount : (mountFromEmpty (X.seed pad)).result.1=afterOne empty (X.seed pad) := by
    rw [mountFromEmpty,(next_job_exact empty (X.seed pad) [] ready).1]
  rw [mount]
  apply real_stack_encoding_from_initial_width X M
  apply afterOne_shape_width
  · intro row h
    exact (List.not_mem_nil h).elim
  · change q≤max q (max (pageKeyWidth m+pad+1) (2^bw))
    exact le_max_left _ _

#print axioms storage_widths_supply_actual_encoding
#print axioms actual_native_count_field_fits_page_word
#print axioms real_stack_encoding_from_initial_width
#print axioms real_stack_encoding_from_singleton_mount
end
end J6R82LeafTime