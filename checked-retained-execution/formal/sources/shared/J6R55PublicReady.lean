import J6R55PublicReserve

/-! Read readiness off the actual source state's first and next issuer.
The executable first counter reads the emitted exterior word, not a
separately supplied copy. A matching raw root-body constructor is a
separate check; this module does not alter a frozen identifier. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R31RootResidentTables J6R50SourceProducer
open J6R51 J6R51Online J6R48DFS J6R54PublicFamily J6R16ModeCost
open J6R12Blueprint J6R10Reachable J6R11Blueprint J6ActiveRun J1PPrinted J6R26DescriptorTree
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 3600
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s oldC key prec tw bw page : ℕ}
variable {cfg : RootBounds s oldC f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {P : Prepared cfg sel root hf} {v : Ticket sel root}

theorem compiled_stored_site_uses_its_input_issuer
    (I : Meter (OccurrenceInput P v key prec tw bw page))
    (S : Meter (StoredSite P v key prec tw bw page)) (exactInput : S.result.input=I.result) :
    S.result.birth.job.identifier=I.result.issued.result ∧
    S.result.birth.issuance.steps=I.result.issued.steps+
      (I.result.native.steps+I.result.physical.steps+I.result.words.steps+4) := by
  change (compileOccurrence S.result.input).job.identifier=_ ∧
    (compileOccurrence S.result.input).issuance.steps=_
  rw [exactInput]
  exact ⟨(occurrence_identity I.result).1,(occurrence_identity I.result).2.2⟩

def UsesFirstIssuer {rate : ℕ} (M : OnlineMachine P key prec tw bw page rate)
    (issued : Meter (Word key)) : Prop :=
  ∀ w, (M.initial w).result.input.issued=issued

def UsesChildIncrement {rate : ℕ} (M : OnlineMachine P key prec tw bw page rate) : Prop :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel root c)
    (u : (Plan sel).Slot c) (w : (Plan sel).Slot ((Plan sel).child c u)),
      (M.demand (sourceState M p u) w).result.event.issued=increment (sourceState M p u).birth.job.identifier

variable {V : Type} [Fintype V] {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {q rr cc dd kp tc tj edgew rate : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable (pad : ℕ)

def issuedAtFirstDepth : Meter (Word (KeyWidth kp tc tj)) :=
  increment (literalSite W C i j g).issue.result

abbrev nativeDepthCapacity :=
  (literalSite W C i j g).issue.result.val-1+pathLimit (physicalSize m native) 2<2^KeyWidth kp tc tj

variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W C i j g).hf}
variable (M : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=m) pad)

theorem real_first_issuer_from_exact_boot
    (S : ∀ w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g),
      Meter (OccurrenceInput T ((Path.root : Path (G.selector ell) (exteriorChild G ell i j g)
        (exteriorChild G ell i j g)).ticket w) (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)))
    (uses : ∀ w, (M.initial w).result.input=(S w).result)
    (emits : ∀ w, (S w).result.issued=issuedAtFirstDepth W C i j g) :
    UsesFirstIssuer M (issuedAtFirstDepth W C i j g) :=
  fun w => (congrArg (fun t=>t.issued) (uses w)).trans (emits w)

theorem real_ready_after_literal_mount
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤C.mark.val)
    (capacity : nativeDepthCapacity W C i j g)
    (first : UsesFirstIssuer M (issuedAtFirstDepth W C i j g)) (later : UsesChildIncrement M) :
    ReadyOnStack (borns M) (actualInstalledBank W C i j g pad B) ∧
      (∀ {c : Call (PhysicalHost f ell)} (p : Path (G.selector ell) (exteriorChild G ell i j g) c)
        (u : (Plan (G.selector ell)).Slot c),
        (borns M p u).job.identifier.val=(literalSite W C i j g).issue.result.val-1+
          ((Plan (G.selector ell)).child c u).depth) := by
  let X := literalSite W C i j g
  let current := X.issue.result
  let offset := current.val-1
  let bank := actualInstalledBank W C i j g pad B
  have depth : (exteriorChild G ell i j g).depth=1 := real_exterior_depth_one X
  have pos : 0<current.val := (Nat.zero_le C.mark.val).trans_lt (emitted_public_root_id_above_mark W C i j g)
  have initialValue : current.val=offset+(exteriorChild G ell i j g).depth := by
    rw [depth]
    change current.val=(current.val-1)+1
    omega
  have rootFit : (exteriorChild G ell i j g).depth≤pathLimit (physicalSize m native) 2 := by
    rw [depth]
    unfold pathLimit
    omega
  have width : 0<KeyWidth kp tc tj := by unfold KeyWidth; omega
  have R : Reserved bank current := (real_public_install_and_reserve W C i j g pad B sync old).2.2
  have oldBound : ∀ row∈bank.headers,row.id.val≤offset+(exteriorChild G ell i j g).depth := by
    rw [←initialValue]
    exact R.2
  have startIds (w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g)) :
      (M.initial w).result.birth.job.identifier=(increment current).result :=
    (occurrence_identity (M.initial w).result.input).1.trans (congrArg Meter.result (first w))
  have proof := online_depth_issuance_and_stack M bank offset current width capacity
    rootFit initialValue R.1 oldBound startIds later
  exact ⟨proof.1,proof.2.1⟩

#print axioms compiled_stored_site_uses_its_input_issuer
#print axioms real_first_issuer_from_exact_boot
#print axioms real_ready_after_literal_mount
end
end J6R55Public

