import J6R64ActiveIncoming
import J6R48DFSScope

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3200
set_option Elab.async false

/-! Same old publisher, sidecar install/mount, and retirement. A
successful continuation receives proof that the current paid header
is at the actual live head; there is no extra lookup or publication.
The dependent proof is erased and is not an additional input tape. -/
namespace J6R64Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48GeneratedAddons J6R50SourceProducer J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R51ParentFrames J6R52CacheSource J6R52CacheWhole J6R48RawRoute

def withScopeHeader {key prec tw bw : ℕ} {D Out : Type}
    (retire : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D → ℕ)
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D) → OwnsHeader j.entry.result R → Meter (Out×Ledger key prec tw bw D))
    (bad : Meter Out) (B : Ledger key prec tw bw D) : Meter (Out×Ledger key prec tw bw D) :=
  let q := j.install B
  if hit : q.result.2=true then
    let out := go q.result.1 (successful_publish_has_exact_head j B hit)
    ⟨(out.result.1,B),q.steps+out.steps+retire j+4⟩
  else ⟨(bad.result,B),q.steps+bad.steps+4⟩

theorem scope_header_same_debit {key prec tw bw : ℕ} {D Out : Type}
    (retire : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D → ℕ)
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : SM (Ledger key prec tw bw D) Out)
    (bad : Meter Out) (B : Ledger key prec tw bw D) :
    withScopeHeader retire j (fun R _=>go R) bad B=J6R48DFS.withScope retire j go bad B := by
  by_cases hit : (j.install B).result.2=true
  · rw [withScopeHeader,J6R48DFS.withScope]
    dsimp only
    rw [dif_pos hit,if_pos hit]
  · rw [withScopeHeader,J6R48DFS.withScope]
    dsimp only
    rw [dif_neg hit,if_neg hit]

theorem scope_header_value {key prec tw bw : ℕ} {D Out : Type}
    (retire : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D → ℕ)
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D) → OwnsHeader j.entry.result R → Meter (Out×Ledger key prec tw bw D))
    (old : SM (Ledger key prec tw bw D) Out)
    (bad : Meter Out) (B : Ledger key prec tw bw D)
    (same : ∀ R own,(go R own).result.1=(old R).result.1) :
    (withScopeHeader retire j go bad B).result=
      (J6R48DFS.withScope retire j old bad B).result := by
  by_cases hit : (j.install B).result.2=true
  · rw [withScopeHeader,J6R48DFS.withScope]
    dsimp only
    rw [dif_pos hit,if_pos hit]
    exact congrArg (fun v=>(v,B)) (same _ _)
  · rw [withScopeHeader,J6R48DFS.withScope]
    dsimp only
    rw [dif_neg hit,if_neg hit]


#print axioms scope_header_same_debit
#print axioms scope_header_value
end J6R64Active

