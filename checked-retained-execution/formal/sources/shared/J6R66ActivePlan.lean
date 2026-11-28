import J6R64ActiveAtPath
import J6R64ActiveExteriorStep
import J6R55CachedLedgerCore

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14500000
set_option maxRecDepth 3500
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! The runtime uses its returned directory head. The comparison
machine below is proof-only: it fills the old active callback ABI
with the proved identical incoming meter, so the actual R55/R56
occurrence accounting can be reused for this new run. -/
namespace J6R66Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R50SourceProducer J6R24MeteredRecursion J6R49DFS
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R64Active J6R62ActivePrep

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "Here" => (Path.root : Path sel r r)

private theorem call_words_ext {x : Call (PhysicalHost f ell)} {pw ew : ℕ}
    (A B : CallWords x pw ew) (hp : A.precision=B.precision) (hm : A.edges=B.edges) : A=B := by
  cases A
  cases B
  cases hp
  cases hm
  rfl

private theorem meter_ext {A : Type} (u v : Meter A)
    (value : u.result=v.result) (charge : u.steps=v.steps) : u=v := by
  cases u
  cases v
  cases value
  cases charge
  rfl

theorem live_incoming_meter_independent_of_tail (X : StoredSite T v key prec tw bw page)
    (B R : L) (atB : OwnsHeader X.birth.job.entry.result B)
    (atR : OwnsHeader X.birth.job.entry.result R) :
    readIncoming X B atB=readIncoming X R atR := by
  let a := readIncoming X B atB
  let b := readIncoming X R atR
  have value : a.result=b.result := by
    apply call_words_ext
    · exact (valued_word a.result.precision).symm.trans
        ((congrArg word (a.result.precisionValue.trans b.result.precisionValue.symm)).trans
          (valued_word b.result.precision))
    · exact (valued_word a.result.edges).symm.trans
        ((congrArg word (a.result.edgesValue.trans b.result.edgesValue.symm)).trans
          (valued_word b.result.edges))
  have fee := (incoming_words_from_published_head X B atB).2.2.trans
    (incoming_words_from_published_head X R atR).2.2.symm
  exact meter_ext a b value fee

/-- A retained layout is chosen for the current actual active site.
It may contain measured access to its already paid retained output;
an independently rebuilt or guessed layout is not inferred here. -/
structure RetainedAfter (T : Prepared cfg sel r hf) (key prec tw bw page q cw : ℕ) where
  fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
    InputFits sel (readyAtPath T p a) q
  layout : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x)
    (_X : StoredSite T (p.ticket w) key prec tw bw page)
    (a : (S).cutoff<((P).child x w).edges),
    Meter (AtLayout sel (readyAtPath T (.step p w) a) cw)

def RetainedAfter.live (F : RetainedAfter T key prec tw bw page q cw) :
    AfterInputs T key prec tw bw page q cw :=
  ⟨F.fit,fun p w X _ _ a=>F.layout p w X a⟩

structure RootInputs (T : Prepared cfg sel r hf) (key prec tw bw page cw ew : ℕ) where
  header : DirRow key
  inherit : (B : PageBank f ell key prec tw bw page) → OwnsHeader header B → Meter (CallWords r prec ew)
  layout : (B : PageBank f ell key prec tw bw page) → OwnsHeader header B → (a : (S).cutoff<r.edges) →
    Meter (AtLayout sel (readyAtPath T Here a) cw)

def rootSetup (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (a : (S).cutoff<r.edges) :
    Meter (ActiveMachine sel (readyAtPath T Here a) T.bank q) :=
  let u := actual_path_taper T Here a
  sharedMachine M.modeWidth (F.fit Here a) u.1 u.2
    (E.inherit B own) (E.layout B own a) (M.activeRoot a)

/-- An equality normal form for the proof adapter only. The real
runner never constructs this synthetic directory or recomputes the
old job to obtain its header. -/
def headNormalForm (X : StoredSite T v key prec tw bw page) : L :=
  ⟨[X.birth.job.entry.result],[]⟩

def summaryAfter (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (p : Path sel r c) (w : (P).Slot c) (X : StoredSite T (p.ticket w) key prec tw bw page)
    (a : (S).cutoff<((P).child c w).edges) :
    Meter (ActiveMachine sel (readyAtPath T (.step p w) a) T.bank q) :=
  preparedAfter M F.live p w X (headNormalForm X) rfl a

theorem real_preparation_is_exact_header_normal_form
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (p : Path sel r c) (w : (P).Slot c) (X : StoredSite T (p.ticket w) key prec tw bw page)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B) (a : (S).cutoff<((P).child c w).edges) :
    preparedAfter M F.live p w X B own a=summaryAfter M F p w X a := by
  have same := live_incoming_meter_independent_of_tail X B (headNormalForm X) own rfl
  unfold summaryAfter preparedAfter RetainedAfter.live
  dsimp only
  rw [same]

/-- Comparison machinery, not an executable alternative. Old scope
loaders and terminal inputs are byte-for-byte unchanged fields. -/
def shadow (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial) : Machine :=
  {M with
    activeRoot := rootSetup M F E initial own
    activeAfter := fun p w X a=>summaryAfter M F p w X a}

theorem shadow_stored_sites_unchanged (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (w : (P).Slot c) :
    sourceState (shadow M F E initial own) p w=sourceState M p w := by
  induction p with
  | root => rfl
  | step p prev ih =>
    change ((M.demand (sourceState (shadow M F E initial own) p prev) w).result.advance).next=
      ((M.demand (sourceState M p prev) w).result.advance).next
    rw [ih prev]

theorem shadow_births_unchanged (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial) :
    @borns f ell s C key prec tw bw page q cfg sel r hf T (shadow M F E initial own)=
      @borns f ell s C key prec tw bw page q cfg sel r hf T M := by
  funext x p w
  unfold borns
  rw [shadow_stored_sites_unchanged]

#print axioms live_incoming_meter_independent_of_tail
#print axioms rootSetup
#print axioms real_preparation_is_exact_header_normal_form
#print axioms shadow_stored_sites_unchanged
#print axioms shadow_births_unchanged
end
end J6R66Active

