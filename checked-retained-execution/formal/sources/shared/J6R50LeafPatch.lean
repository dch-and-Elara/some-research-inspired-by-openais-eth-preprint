import J6R49DFSRun

/-! A metered compiled leaf can replace exactly one reached slot in the
existing scoped runner. The active body, installed births and stable
root are preserved. A missing patch uses the existing leaf unchanged. -/
namespace J6R50Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime J6ActiveRun J6R10Repack J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R16ModeCost J6R22Active J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R49DFS
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000
set_option maxRecDepth 2700

def attemptedOr {A : Type} (attempt : Meter (Option A)) (fallback : Unit→Meter A) : Meter A :=
  match attempt.result with
  | none =>
    let out := fallback ()
    ⟨out.result,attempt.steps+out.steps+4⟩
  | some value => ⟨value,attempt.steps+3⟩

theorem attemptedOr_success {A : Type} (attempt : Meter (Option A)) (fallback : Unit→Meter A)
    (value : A) (arrived : attempt.result=some value) :
    attemptedOr attempt fallback=⟨value,attempt.steps+3⟩ := by
  unfold attemptedOr
  rw [arrived]

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}

structure LeafPatch (R : StreamingResident T key prec tw bw page q)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) where
  positive : 0<c.edges
  attempt : PageBank f ell key prec tw bw page→Meter (Option (Block (T.frame p.reached) ell))
  exactRead : ∀ B,opened R.births R.rootLive p B→
    ∃ value,(attempt B).result=some value ∧
      (T.frame p.reached).decode value=(T.frame p.reached).decode (T.run c p.reached).result

variable (R : StreamingResident T key prec tw bw page q)
variable (choose : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c),
  c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff→Option (LeafPatch R p))

noncomputable def installLeafPatch : StreamingResident T key prec tw bw page q where
  modeWidth := R.modeWidth
  births := R.births
  rootLive := R.rootLive
  rootStable := R.rootStable
  active := R.active
  leaf p stop B :=
    match choose p stop with
    | none => R.leaf p stop B
    | some work => attemptedOr (work.attempt B) (fun _=>R.leaf p stop B)
  leafMatches p stop B alive := by
    cases hw : choose p stop with
    | none => exact R.leafMatches p stop B alive
    | some work =>
      obtain ⟨value,someValue,exactValue⟩ := work.exactRead B alive
      change (T.frame p.reached).decode
        (attemptedOr (work.attempt B) (fun _=>R.leaf p stop B)).result=_
      rw [attemptedOr_success _ _ value someValue]
      exact exactValue

theorem patched_stopping_word {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (stop : c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (B : PageBank f ell key prec tw bw page) (alive : opened R.births R.rootLive p B)
    (work : LeafPatch R p) (present : choose p stop=some work) :
    ∃ value,(installLeafPatch R choose).leaf p stop B=⟨value,(work.attempt B).steps+3⟩ ∧
      (T.frame p.reached).decode value=(T.frame p.reached).decode (T.run c p.reached).result := by
  obtain ⟨value,someValue,exactValue⟩ := work.exactRead B alive
  refine ⟨value,?_,exactValue⟩
  change (match choose p stop with
    | none=>R.leaf p stop B
    | some A=>attemptedOr (A.attempt B) (fun _=>R.leaf p stop B))=_
  rw [present]
  exact attemptedOr_success _ _ value someValue

theorem unpatched_stopping_word {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (stop : c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (B : PageBank f ell key prec tw bw page) (absent : choose p stop=none) :
    (installLeafPatch R choose).leaf p stop B=R.leaf p stop B := by
  change (match choose p stop with
    | none=>R.leaf p stop B
    | some A=>attemptedOr (A.attempt B) (fun _=>R.leaf p stop B))=_
  rw [absent]

theorem zero_edge_leaf_falls_back {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (stop : c.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (B : PageBank f ell key prec tw bw page) (empty : c.edges=0) :
    (installLeafPatch R choose).leaf p stop B=R.leaf p stop B := by
  apply unpatched_stopping_word
  cases matchChoice : choose p stop with
  | none => rfl
  | some work => exact (Nat.ne_of_gt work.positive empty).elim

#print axioms attemptedOr_success
#print axioms installLeafPatch
#print axioms patched_stopping_word
#print axioms unpatched_stopping_word
#print axioms zero_edge_leaf_falls_back
end J6R50Leaf
