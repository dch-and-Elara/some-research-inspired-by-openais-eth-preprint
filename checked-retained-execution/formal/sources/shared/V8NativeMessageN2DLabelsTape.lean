import V8NativeMessageN2DLabelsCore
import J6R12CollisionPacking

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000
set_option linter.unusedSectionVars false

/-! Recover the certificate on the same actual full-64 label tape
used in the rounded physical placement. The format and complete
vertex order are supplied; no label list and no balancing bound are
supplied by the caller. -/
namespace V8NativeMessage.N2DLabels
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionSource J6R12CollisionPacking
open J6R11Collision J6R11CollisionGreedy J6R11CollisionReindex J6R10Repack P11FullPacking

private theorem map_recovers_roster {V A B : Type*} (xs : List V) (p q : V→A) (enc : A→B)
    (inj : Function.Injective enc) (eq : xs.map (fun v=>enc (p v))=xs.map (fun v=>enc (q v))) :
    ∀ v∈xs,p v=q v := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.cons.injEq] at eq
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · exact inj eq.1
    · exact ih eq.2 v hv

variable {E R C : Type*} [Fintype E] {N : Network E R C} {a : ℕ}

structure Full64Input (N : Network E R C) (a : ℕ) where
  format : Format E R C (Fin a→Fin 64)
  rowExact : format.row=N.row
  colExact : format.col=N.col
  labelWidth : format.b=6*a
  order : List (R⊕C)
  distinct : order.Nodup
  complete : ∀ v,v∈order

theorem label_bytes_injective (I : Full64Input N a) : Function.Injective I.format.label := by
  intro x y eq
  apply I.format.aInj
  have e := congrArg bitsValue eq
  change bitsValue (encodeBits I.format.b (I.format.aCode x))=
    bitsValue (encodeBits I.format.b (I.format.aCode y)) at e
  rwa [encodeBits_exact _ _ (I.format.aFit x),encodeBits_exact _ _ (I.format.aFit y)] at e

def Full64Input.raw (I : Full64Input N a) : List (List Bool×List Bool) :=
  I.format.edges.map (fun e=> (encodeBits I.format.kR (I.format.rCode (I.format.row e)),
    encodeBits I.format.kC (I.format.cCode (I.format.col e))))

def Full64Input.run (I : Full64Input N a) : Meter (List EdgeTape×List (List Bool)) :=
  let F := I.format
  let init := initGraph F.kR F.kC I.raw
  let out := drive F.e F.kR F.kC F.b (I.order.map F.target) init.result
  ⟨out.result,init.steps+out.steps⟩

variable [Fintype R] [Fintype C]

def Full64Input.fee (I : Full64Input N a) : ℕ :=
  (2*I.format.kR+2*I.format.kC+14)*Fintype.card E+
   ((I.format.stepBound (2^(6*a))+2*I.format.b+6)*(Fintype.card R+Fintype.card C)+
     16*(I.format.b+1)*2^(6*a)+12*I.format.width+20)

theorem full64_run_payload (I : Full64Input N a) :
    I.run.result= (drive I.format.e I.format.kR I.format.kC I.format.b
      (I.order.map I.format.target) (I.format.graph (fun _=>none))).result := by
  unfold Full64Input.run Full64Input.raw
  dsimp only
  rw [(initGraph_exact I.format).1]

def wordsOf (P : PhysicalPacking N a (Fin 64)) : R⊕C→Fin a→Fin 64 :=
  Sum.elim P.rowLabel P.colLabel

/-- For the named same packing, equality of the actual complete emitted
label file suffices to recover both the original collision statistic and
the matching final incidence tape. Seat order is not used. -/
theorem exact_output_recovers_certificate (I : Full64Input N a) (Δ : ℕ)
    (hr : ∀ v,Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v,Nat.card {e : E // N.col e=v}≤Δ)
    (P : PhysicalPacking N a (Fin 64))
    (same : I.run.result.2=I.order.map (fun v=>I.format.label (wordsOf P v))) :
    CollisionCertified Δ P ∧ I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)) := by
  have rb (v : R) : (fibre I.format.row v).card≤Δ := by
    rw [I.rowExact,card_filter_fibre]
    exact hr v
  have cb (v : C) : (fibre I.format.col v).card≤Δ := by
    rw [I.colExact,card_filter_fibre]
    exact hc v
  obtain ⟨z,graph,word,bal,_⟩ := source_64 a (Fintype.card_fin 64) I.format
    I.labelWidth I.order I.distinct I.complete Δ rb cb
  rw [full64_run_payload I,word] at same
  have point : z=wordsOf P := funext fun v=>
    map_recovers_roster I.order z (wordsOf P) I.format.label (label_bytes_injective I) same v (I.complete v)
  have hword : splitSample z=(P.rowLabel,P.colLabel) := congrArg splitSample point
  constructor
  · unfold CollisionCertified
    rw [I.rowExact,I.colExact,←declared_variance_eq N (splitSample z),hword] at bal
    rw [Nat.card_eq_fintype_card]
    exact bal
  · rw [full64_run_payload I,graph,point]

structure ObservedPacking (I : Full64Input N a) (Δ : ℕ) where
  pack : CertifiedPacking N a Δ
  rounded : RoundsExactly pack.val
  labelFile : I.run.result.2=I.order.map (fun v=>I.format.label (wordsOf pack.val v))
  incidenceFile : I.run.result.1=I.format.graph (fun v=>some (wordsOf pack.val v))
  cost : I.run.steps≤I.fee

/-- Use the actual R12 rounded placement theorem, not a separate
balance witness which may have different labels on the same graph. -/
theorem actual_full64_packing (I : Full64Input N a) (Δ : ℕ)
    (hr : ∀ v,Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v,Nat.card {e : E // N.col e=v}≤Δ)
    (space : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (slots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E) :
    Nonempty (ObservedPacking I Δ) := by
  obtain ⟨P,words,round,fee⟩ := actual_labels_feed_packing N I.format I.rowExact I.colExact
    (Fintype.card_fin 64) I.labelWidth I.order I.distinct I.complete Δ hr hc space slots
  have hw : I.run.result.2=I.order.map (fun v=>I.format.label (wordsOf P v)) := words
  obtain ⟨good,incidence⟩ := exact_output_recovers_certificate I Δ hr hc P hw
  exact ⟨⟨⟨P,good⟩,round,hw,incidence,fee⟩⟩

#print axioms label_bytes_injective
#print axioms full64_run_payload
#print axioms exact_output_recovers_certificate
#print axioms actual_full64_packing
end V8NativeMessage.N2DLabels
