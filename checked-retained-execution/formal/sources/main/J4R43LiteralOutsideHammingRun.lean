import J4R43LiteralOutsideReceipt

/-! Exact positive extreme readout by integer comparison. The counter
pays one comparison and at most one multiplication per candidate,
using the graph-only no-sign contraction as its starting value. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6ActiveRun J6R12Blueprint J6R9Recursive 
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4500000

structure HammingRun where
  index : ℕ
  comparisons : ℕ
  products : ℕ

/-- With one candidate remaining, return that comparison or the failure
index without computing a never-read next power. -/
def hammingRun (z base start : ℤ) : ℕ→HammingRun
  | 0 => ⟨0,0,0⟩
  | 1 => if z=start then ⟨0,1,0⟩ else ⟨1,1,0⟩
  | n+2 => if z=start then ⟨0,1,0⟩ else
      let R := hammingRun z base (start*base) (n+1)
      ⟨R.index+1,R.comparisons+1,R.products+1⟩

theorem hamming_run_correct (base start : ℤ) (b : 1<base) (a : 0<start)
    {n j : ℕ} (h : j<n) :
    (hammingRun (start*base^j) base start n).index=j := by
  induction n generalizing j start with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => cases n <;> simp [hammingRun]
    | succ j =>
      cases n with
      | zero => omega
      | succ n =>
        have miss : start*base^(j+1)≠start := by
          intro E
          have bad := hamming_comparison_unique start base a b (show start*base^(j+1)=start*base^0 by simpa using E)
          omega
        have vals : start*base^(j+1)=(start*base)*base^j := by
          rw [pow_succ']; ring
        have pos : 0<start*base := mul_pos a (by omega)
        have K := ih (start:=start*base) pos (j:=j) (by omega)
        simp only [hammingRun,if_neg miss]
        rw [vals,K]

theorem hamming_run_fees (z base start : ℤ) (n : ℕ) :
    (hammingRun z base start n).comparisons≤n ∧
      (hammingRun z base start n).products≤n-1 := by
  induction n generalizing start with
  | zero => simp [hammingRun]
  | succ n ih =>
    cases n with
    | zero => simp [hammingRun]; split <;> decide
    | succ n =>
      have q := ih (start*base)
      dsimp only [hammingRun]
      split <;> dsimp only <;> omega

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ}
local notation "N" => oldColumnNetwork F reg

theorem every_candidate_is_real_input (P : PhysicalPacking N a (Fin 64)) (t : ℤ) {j : ℕ}
    (h : j≤(hitPins F reg P t).card) :
    ∃ σ : W→Bool,hitWeight F reg P t σ=j := by
  obtain ⟨T,sub,c⟩ := Finset.exists_subset_card_eq h
  refine ⟨fun w=>decide (w∈T),?_⟩
  unfold hitWeight
  suffices H : (hitPins F reg P t).filter (fun v=>decide (v∈T)=true)=T by rw [H,c]
  ext w
  simp only [Finset.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun e=>⟨sub e,e⟩⟩

theorem actual_positive_candidates_fit (P : PhysicalPacking N a (Fin 64)) {j : ℕ}
    (h : j≤(hitPins F reg P (((2^a:ℕ):ℤ)-1)).card) :
    let C := J9FactorBounds.kernel (2^a)
    let t := (((2^a:ℕ):ℤ)-1)
    |graphFactor F reg P t C*(1-C)^j|≤(2:ℤ)^(7*Fintype.card (DWire F)) := by
  obtain ⟨σ,e⟩ := every_candidate_is_real_input F reg P _ h
  have z := literal_hamming_factorization F reg P (((2^a:ℕ):ℤ)-1)
    (J9FactorBounds.kernel (2^a)) σ
  rw [e] at z
  dsimp only
  rw [←z]
  exact actual_integer_has_height F reg P σ

theorem graph_only_seed_is_literal_read (P : PhysicalPacking N a (Fin 64)) (t κ : ℤ) :
    graphFactor F reg P t κ=factorizedValue F reg P t κ (fun _=>false) := by
  rw [literal_hamming_factorization]
  simp [hitWeight]

variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0

theorem decode_actual_outer_hamming (P : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (out : t.val=(((2^a₀:ℕ):ℤ)-1)) (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    let p := registerPrecision S root t
    let C := J9FactorBounds.kernel (2^a₀)
    let A := factorizedValue F reg P t.val C (fun _=>false)
    let n := (hitPins F reg P t.val).card
    let z := V8NativeMessage.N7HighBound.centeredBox p f hf
      (originalOppositeSlot F reg P d t i hv 0 0 hf σ)
    let run := hammingRun z (1-C) A (n+1)
    run.index=hitWeight F reg P t.val σ ∧ run.comparisons≤n+1 ∧ run.products≤n := by
  let C : ℤ := J9FactorBounds.kernel (2^a₀)
  let A : ℤ := factorizedValue F reg P t.val C (fun _=>false)
  let n := (hitPins F reg P t.val).card
  let p := registerPrecision S root t
  let z := V8NativeMessage.N7HighBound.centeredBox p f hf
    (originalOppositeSlot F reg P d t i hv 0 0 hf σ)
  obtain ⟨_,r,pos,base⟩ := original_positive_extreme_is_integer F reg P G d t i hv out hf hd σ
  have seed : graphFactor F reg P t.val C=A := graph_only_seed_is_literal_read F reg P t.val C
  have range : hitWeight F reg P t.val σ<n+1 := (hamming_le_selected F reg P t.val σ).trans_lt (by omega)
  have z' : z=A*(1-C)^hitWeight F reg P t.val σ := by
    change z=graphFactor F reg P t.val C*(1-C)^hitWeight F reg P t.val σ at r
    rwa [seed] at r
  refine ⟨?_,(hamming_run_fees z (1-C) A (n+1)).1,?_⟩
  · change (hammingRun z (1-C) A (n+1)).index=hitWeight F reg P t.val σ
    rw [z']
    apply hamming_run_correct (1-C) A base _ range
    exact seed ▸ pos
  · simpa only [Nat.add_sub_cancel] using (hamming_run_fees z (1-C) A (n+1)).2

#print axioms hamming_run_correct
#print axioms hamming_run_fees
#print axioms every_candidate_is_real_input
#print axioms actual_positive_candidates_fit
#print axioms graph_only_seed_is_literal_read
#print axioms decode_actual_outer_hamming
end
end J4R43LiteralOutside

