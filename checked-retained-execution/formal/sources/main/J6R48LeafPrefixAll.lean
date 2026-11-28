import J6R48LeafExecution
import J6R48LeafBankPrefix

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000
set_option maxRecDepth 2400

/-! An unrelated real chronological prefix increases the complete leaf
meter once per generated record per Boolean assignment. Word values,
old creation tags, and all additions/multiplications are unchanged. -/
namespace J6R48Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6ActiveRun J6R10Repack J6R11Blueprint J6R21Leaf J6R21Ancestor J6R22Active
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage

private theorem add_bumped {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (a b : Meter (UVBlock fw ell)) (x y : ℕ) :
    addM hp (bump a x) (bump b y)=bump (addM hp a b) (x+y) := by
  unfold addM bump
  dsimp only
  congr 1
  omega

private theorem mul_bumped {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (a b : Meter (UVBlock fw ell)) (x y : ℕ) :
    mulM hp (bump a x) (bump b y)=bump (mulM hp a b) (x+y) := by
  unfold mulM bump
  dsimp only
  congr 1
  omega

private theorem pad_bumped {A : Type*} (a : Meter A) (t u : ℕ) :
    padCost (bump a t) u=bump (padCost a u) t := by
  unfold padCost bump
  dsimp only
  congr 1
  omega

theorem exact_list_overhead {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hl : 0<ell) {A : Type}
    (f g : A→Meter (UVBlock fw ell)) (charge : A→ℕ) (xs : List A)
    (isBump : ∀ a∈xs,g a=bump (f a) (charge a)) :
    foldM hp he hl g xs=bump (foldM hp he hl f xs) ((xs.map charge).sum) := by
  induction xs with
  | nil => simp [foldM,bump]
  | cons a as ih =>
    simp only [foldM,List.map_cons,List.sum_cons]
    rw [isBump a List.mem_cons_self,ih (fun b hb=>isBump b (List.mem_cons_of_mem _ hb)),
      mul_bumped]

theorem exact_clock_overhead {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (f g : List Bool→Meter (UVBlock fw ell)) (d : ℕ)
    (each : ∀ x,g x=bump (f x) d) (clock : List Unit) (rev : List Bool) :
    clockDFS hp g clock rev=bump (clockDFS hp f clock rev) (2^clock.length*d) := by
  induction clock generalizing rev with
  | nil => simp [clockDFS,each,pad_bumped]
  | cons u us ih =>
    simp only [clockDFS,ih,add_bumped,pad_bumped,List.length_cons]
    congr 1
    rw [pow_succ]
    ring

def codeKey {m key page : ℕ} : PageReadCode m key page→Option (J6R15ModeCost.Word key)
  | .original _ _=>none
  | .generated id _ _ _=>some id

def generationUnits {m key page : ℕ} : PageReadCode m key page→ℕ
  | .original _ _=>0
  | .generated _ _ _ _=>1

private theorem list_mul_sum {A : Type*} (l : List A) (f : A→ℕ) (n : ℕ) :
    (l.map (fun a=>f a*n)).sum=(l.map f).sum*n := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons,List.sum_cons,ih,Nat.add_mul]

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
variable {c : Call (PhysicalHost f ell)}
local notation "Bnk" => PageBank f ell key prec tw bw page
local notation "Rec" => Stored key prec tw bw (PagedEnvelope f ell prec page)

def generatedRecordCount (D : RawTape c key page) : ℕ :=
  (D.rows.map (fun row=>generationUnits row.2)).sum

theorem actual_raw_leaf_front_surcharge (D : RawTape c key page) (hf : f.Monic)
    (F : Frame f c.prec) (hEll : 0<ell)
    (before after : Bnk) (front : List (RefRow key Rec))
    (grown : after.records=front++before.records)
    (away : ∀ r∈front,∀ row∈D.rows,codeKey row.2≠some r.address) :
    runTape D hf F hEll after=bump (runTape D hf F hEll before)
      (2^c.edges*(generatedRecordCount D*(front.length*refHeadFee key))) := by
  let q : ℕ := front.length*refHeadFee key
  let fee (r : (c.host.Row⊕c.host.Col)×PageReadCode c.edges key page) := generationUnits r.2*q
  have each (xs : List Bool) :
      readProduct F.hp F.sizePos hEll D.rows (fun r=>r.2.run hf F hEll after) xs =
        bump (readProduct F.hp F.sizePos hEll D.rows (fun r=>r.2.run hf F hEll before) xs)
          (generatedRecordCount D*q) := by
    unfold readProduct generatedRecordCount
    rw [← list_mul_sum D.rows (fun r=>generationUnits r.2) q]
    apply exact_list_overhead F.hp F.sizePos hEll _ _ fee
    rintro ⟨v,k⟩ mem
    cases k with
    | original w tape => simp [fee,generationUnits,PageReadCode.run,bump]
    | generated id pg dp ws =>
      have pass : ∀ e∈front,e.address≠id := fun e he eq=>
        away e he ⟨v,PageReadCode.generated id pg dp ws⟩ mem (congrArg some eq.symm)
      simpa only [fee,generationUnits,Nat.one_mul,PageReadCode.run,q] using
        read_page_grown hf F hEll id pg dp ws xs before after front grown pass
  have charged := exact_clock_overhead F.hp _ _ (generatedRecordCount D*q) each D.clock []
  simpa only [runTape,D.clockExact] using charged

theorem exact_leaf_price_after_actual_jobs (D : RawTape c key page) (hf : f.Monic)
    (F : Frame f c.prec) (hEll : 0<ell) (before : Bnk)
    (jobs : List (PageJob f ell key prec tw bw page))
    (away : ∀ j∈jobs,∀ row∈D.rows,codeKey row.2≠some j.identifier) :
    runTape D hf F hEll (afterJobs before jobs)=bump (runTape D hf F hEll before)
      (2^c.edges*(generatedRecordCount D*(jobs.length*refHeadFee key))) := by
  have same := actual_raw_leaf_front_surcharge D hf F hEll before (afterJobs before jobs)
    (jobs.map Job.immutable).reverse (after_jobs_views before jobs).2 ?_
  · simpa only [List.length_reverse,List.length_map] using same
  · intro e he
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    exact away j hj

#print axioms exact_list_overhead
#print axioms exact_clock_overhead
#print axioms actual_raw_leaf_front_surcharge
#print axioms exact_leaf_price_after_actual_jobs
end J6R48Leaf
