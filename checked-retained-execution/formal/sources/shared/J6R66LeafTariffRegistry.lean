import J6R48DFSScope
import J6R50PeakStartPrecision
import J6R30ProducedGateRegistryPrefix

/-! The reached directory tariff has a small canonical input. Liveness
alone is weaker: a fixed resident reference can require arbitrarily many
irrelevant scans unless initial scope size is controlled. -/
namespace J6R66LeafTariff
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J1PPrinted J6R12Blueprint J6R24MeteredRecursion J6R16ModeCost J6R48DFS J6R50Peak
open J6ActiveRun J6R11Blueprint

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "Bank" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

/-- This is the actual paid singleton installation, not a newly supplied
live bank. The latter is allowed but has a different tariff. -/
def mountFromEmpty (seed : J) := seed.install (⟨[],[]⟩ : Bank)

theorem actual_empty_mount (seed : J) :
    (mountFromEmpty seed).result.2=true ∧
      IsLive seed (mountFromEmpty seed).result.1 ∧
      (mountFromEmpty seed).result.1.synced ∧
      (mountFromEmpty seed).result.1.records.length=1 := by
  let empty : Bank := ⟨[],[]⟩
  have ready : JobsReady empty [seed] := by
    refine ⟨rfl,by simp,?_⟩
    intro j hj row atRow
    have h : row∈([] : List (DirRow key)) := atRow
    exact (List.not_mem_nil h).elim
  rw [mountFromEmpty,(next_job_exact empty seed [] ready).1]
  exact ⟨rfl,new_is_live seed empty,(after_jobs_synced empty rfl [seed]),rfl⟩

theorem reached_original_mount_record_count (seed : J)
    (born : Births T key prec tw bw page) (p : Path sel r c) :
    (stackBank born (mountFromEmpty seed).result.1 p).records.length=1+moves p ∧
    (stackBank born (mountFromEmpty seed).result.1 p).records.length≤1+pathLimit s C := by
  have count := (stack_directory_size born (mountFromEmpty seed).result.1 p).2
  rw [(actual_empty_mount seed).2.2.2] at count
  exact ⟨count,count.trans_le (Nat.add_le_add_left
    (actual_ancestry_moves_any_start cfg sel T.rootStable p) _)⟩

/-- Earlier irrelevant records may have the same irrelevant key. The
actual lookup, not merely its worst-case tariff, increases linearly. -/
theorem fixed_resident_can_have_unbounded_lookup {D : Type}
    (B : Ledger key prec tw bw D) (sync : B.synced)
    (addr : Word key) (other : RefRow key (Stored key prec tw bw D))
    (h : DirRow key) (paired : h.id=other.address) (away : other.address≠addr) (n : ℕ) :
    let B' : Ledger key prec tw bw D :=
      ⟨List.replicate n h++B.headers,List.replicate n other++B.records⟩
    B'.synced ∧
    (locate addr B'.records).result=(locate addr B.records).result ∧
    (locate addr B'.records).steps=n*refHeadFee key+(locate addr B.records).steps := by
  have eq := reference_front_fee addr (List.replicate n other) B.records
    (fun row hr=>by rw [List.eq_of_mem_replicate hr]; exact away)
  rw [List.length_replicate] at eq
  constructor
  · change (List.replicate n h++B.headers).map DirRow.id=
      (List.replicate n other++B.records).map RefRow.address
    rw [List.map_append,List.map_append,List.map_replicate,List.map_replicate,paired,sync]
  · dsimp only
    rw [eq]
    exact ⟨rfl,rfl⟩

#print axioms actual_empty_mount
#print axioms reached_original_mount_record_count
#print axioms fixed_resident_can_have_unbounded_lookup
end J6R66LeafTariff
