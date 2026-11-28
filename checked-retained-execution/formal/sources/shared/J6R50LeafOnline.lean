import J6R50LeafRead
import J6R48LeafExecution

/-! Produce a leaf program once from a paid physical key-book and the
resident origin byte tables. The output replay is exactly the old raw
leaf interpreter, without assuming that its command tape was given to
the online runner. The reference raw tape occurs only in the theorem. -/
namespace J6R50Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Leaf J6R21Ancestor J6R27OriginalGate
open J6ActiveRun J6R10Repack J6R11Blueprint J6R22Active J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48Leaf
open A1R10 A1R11 A1R12
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17500000

def makeClock {w : ℕ} : List (J6R15ModeCost.Word w) → Meter (List Unit)
  | [] => ⟨[],2⟩
  | _::rest =>
    let r := makeClock rest
    ⟨()::r.result,r.steps+4⟩

theorem make_clock_exact {w : ℕ} (keys : List (J6R15ModeCost.Word w)) :
    makeClock keys=⟨List.replicate keys.length (),4*keys.length+2⟩ := by
  induction keys with
  | nil => rfl
  | cons a rest ih =>
    simp only [makeClock,ih,List.length_cons,List.replicate_succ]
    congr 1

def buyRows {own w key prec page : ℕ} (N b : ℕ) (keys : List (J6R15ModeCost.Word w))
    (lines : List (ResidentPort own w)) (table : OriginTable own w key prec page)
    (roster : List (J6R15ModeCost.Word own)) : Meter (Option (List (ReadCmd key page))) :=
  gatherOptions 1 (buildOwner N b keys lines table) roster

def runRows {f : ℤ[X]} {p ell key prec tw bw page : ℕ}
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (clock : List Unit) (rows : List (ReadCmd key page)) : Meter (Block F ell) :=
  clockDFS F.hp (readProduct F.hp F.sizePos pos rows (fun r=>r.read hf F pos B)) clock []

theorem run_rows_is_raw {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    {c : Call (PhysicalHost f ell)}
    (hf : f.Monic) (F : Frame f c.prec) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (D : RawTape c key page) :
    runRows hf F pos B D.clock (D.rows.map (fun r=>eraseCode r.2))=runTape D hf F pos B := by
  unfold runRows runTape
  congr 1
  funext bits
  rw [readProduct_mapped F.hp F.sizePos pos]
  congr 1
  funext row x
  exact erase_read_exact row.2 hf F pos B x

def onlineLeaf {f : ℤ[X]} {p ell own w key prec tw bw page : ℕ}
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (N b : ℕ) (book : Meter (List (J6R15ModeCost.Word w))) (lines : List (ResidentPort own w))
    (table : OriginTable own w key prec page) (roster : List (J6R15ModeCost.Word own)) :
    Meter (Option (Block F ell)) :=
  let clock := makeClock book.result
  let code := buyRows N b book.result lines table roster
  match code.result with
  | none => ⟨none,book.steps+clock.steps+code.steps+5⟩
  | some ready =>
    let r := runRows hf F pos B clock.result ready
    ⟨some r.result,book.steps+clock.steps+code.steps+r.steps+7⟩

theorem buy_rows_from_real_roster {A : Type*} {own w key prec page : ℕ} (N b : ℕ)
    (keys : List (J6R15ModeCost.Word w)) (lines : List (ResidentPort own w))
    (table : OriginTable own w key prec page) (xs : List A)
    (name : A→J6R15ModeCost.Word own) (cmd : A→ReadCmd key page)
    (checked : ∀ x∈xs,(buildOwner N b keys lines table (name x)).result=some (cmd x)) :
    buyRows N b keys lines table (xs.map name)=⟨some (xs.map cmd),
      3+(xs.map (fun x=>(buildOwner N b keys lines table (name x)).steps+7)).sum⟩ := by
  unfold buyRows
  have e : gatherOptions 1 (buildOwner N b keys lines table) (xs.map name)=
      gatherOptions 1 (fun x=>buildOwner N b keys lines table (name x)) xs := by
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.map_cons,gatherOptions,ih (fun x hx=>checked x (List.mem_cons_of_mem a hx))]
  rw [e,gather_options_exact 1 _ cmd xs checked]

private theorem unit_tape (xs : List Unit) : List.replicate xs.length ()=xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    cases a
    simp only [List.length_cons,List.replicate_succ,ih]

theorem online_leaf_replays_raw {f : ℤ[X]} {ell own w key prec tw bw page : ℕ}
    {c : Call (PhysicalHost f ell)} (hf : f.Monic) (F : Frame f c.prec) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page) (D : RawTape c key page)
    (b : ℕ) (book : Meter (List (J6R15ModeCost.Word w))) (width : book.result.length=c.edges)
    (lines : List (ResidentPort own w)) (table : OriginTable own w key prec page)
    (name : (c.host.Row⊕c.host.Col)→J6R15ModeCost.Word own)
    (loaded : ∀ x∈D.rows,(buildOwner c.edges b book.result lines table (name x.1)).result=
      some (eraseCode x.2))
    (form : HasResidentFormat D B) :
    let op := onlineLeaf hf F pos B c.edges b book lines table (D.rows.map (name∘Prod.fst))
    op.result=some (runTape D hf F pos B).result ∧
    op.steps≤book.steps+4*c.edges+12+
      (D.rows.map (fun x=>(buildOwner c.edges b book.result lines table (name x.1)).steps+7)).sum+
      rawLeafCap F.words.length ell c.prec c.edges D.rows.length (prepriced D F B) F.hp := by
  have h := buy_rows_from_real_roster c.edges b book.result lines table D.rows
    (name∘Prod.fst) (fun r=>eraseCode r.2) loaded
  have clock : makeClock book.result=⟨D.clock,4*c.edges+2⟩ := by
    rw [make_clock_exact,width,← D.clockExact,unit_tape]
  have eval := raw_leaf_steps D hf F pos B form
  unfold onlineLeaf
  rw [clock,h]
  dsimp only
  rw [run_rows_is_raw hf F pos B D]
  constructor
  · rfl
  · simp only [Function.comp_apply]
    omega

#print axioms make_clock_exact
#print axioms run_rows_is_raw
#print axioms buy_rows_from_real_roster
#print axioms online_leaf_replays_raw
end J6R50Leaf
