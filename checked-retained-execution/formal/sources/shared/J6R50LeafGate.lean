import J6R27OriginalGateRun
import J6R49LeafOriginal

/-! The leaf original-gate emitter consumes source syntax with physical
edge keys, not the ordinal bits consumed by the evaluator. Each address
is computed using the actual ordered edge book and paid ripple scan. -/
namespace J6R50Leaf
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Leaf J6R21Ancestor
open J6R27OriginalGate J6OrientedHost
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000

def portOrdinalFee (w b N : ℕ) : ℕ := N*missFee w b+hitFee w b+b+3

theorem current_named_ordinal {w b N : ℕ}
    (hb : 0<b) (fit : N≤2^b) (keys : List (Word w)) (keyAt : Fin N→Word w)
    (inj : Function.Injective keyAt) (real : keys=List.ofFn keyAt) (j : Fin N) :
    let r := findOrdinal b (keyAt j) keys
    r.result=some (word j.val) ∧ r.steps≤portOrdinalFee w b N := by
  dsimp only
  rw [real,find_ordinal_indexed hb keyAt inj fit j]
  exact ⟨rfl,Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right (missFee w b) j.isLt.le) _) _) _⟩

def compileCurrentGate {w : ℕ} (b : ℕ) (keys : List (Word w)) :
    CodeGate (Word w) → Meter (Option (CodeGate (Word b)))
  | .free => ⟨some .free,2⟩
  | .equal ports =>
    let rd := gatherOptions b (fun u=>findOrdinal b u keys) ports
    ⟨rd.result.map CodeGate.equal,rd.steps+4⟩
  | .clause ports signs =>
    let rd := gatherOptions b (fun u=>findOrdinal b u keys) ports
    let cp := copyBytes signs
    ⟨rd.result.map (fun ds=>CodeGate.clause ds cp.result),rd.steps+cp.steps+4⟩

def currentGateFee (w b N d : ℕ) := 8+d*(portOrdinalFee w b N+b+9)

theorem current_source_gate {w b N d : ℕ}
    (hb : 0<b) (fit : N≤2^b) (keys : List (Word w))
    (keyAt : Fin N→Word w) (inj : Function.Injective keyAt) (real : keys=List.ofFn keyAt)
    (slot : Fin d→Fin N) (G : Gate d) :
    let built := compileCurrentGate b keys (encodeGate (keyAt∘slot) G)
    built.result=some (forgetGate (gateTape fit slot G)) ∧
    built.steps≤currentGateFee w b N d := by
  let ids := List.ofFn (keyAt∘slot)
  let addr := (List.ofFn slot).map (fun j=>word (q:=b) j.val)
  have hit (j : Fin N) := current_named_ordinal hb fit keys keyAt inj real j
  have H : (gatherOptions b (fun u=>findOrdinal b u keys) ids).result=some addr := by
    have e := gather_options_exact b (fun j : Fin N=>findOrdinal b (keyAt j) keys)
      (fun j=>word (q:=b) j.val) (List.ofFn slot) (fun j _=>(hit j).1)
    have eq (xs : List (Fin N)) :
        gatherOptions b (fun u=>findOrdinal b u keys) (xs.map keyAt)=
        gatherOptions b (fun j=>findOrdinal b (keyAt j) keys) xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.map_cons,gatherOptions,ih]
    change (gatherOptions b (fun u=>findOrdinal b u keys)
      (List.ofFn (keyAt∘slot))).result=some addr
    rw [← List.map_ofFn,eq,e]
  have C : (gatherOptions b (fun u=>findOrdinal b u keys) ids).steps≤
      3+d*(portOrdinalFee w b N+b+6) := by
    have z := gather_options_bound b (portOrdinalFee w b N)
      (fun u=>findOrdinal b u keys) ids (by
        intro u h
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
        exact (hit (slot j)).2)
    simpa only [ids,List.length_ofFn] using z
  have A : addr=List.ofFn (fun j=>word (q:=b) (slot j).val) := List.map_ofFn slot _
  have eq := exact_code_is_forgotten (b:=b) fit slot G
  rw [← eq]
  cases G with
  | free => exact ⟨rfl,by change 2≤8+_; omega⟩
  | equal =>
    constructor
    · change (gatherOptions b (fun u=>findOrdinal b u keys) ids).result.map CodeGate.equal
        = some (.equal (List.ofFn (fun j=>word (slot j).val)))
      rw [H,A]
      rfl
    · change (gatherOptions b (fun u=>findOrdinal b u keys) ids).steps+4≤currentGateFee w b N d
      unfold currentGateFee
      simp only [Nat.mul_add] at C ⊢
      omega
  | clause signs =>
    constructor
    · change (gatherOptions b (fun u=>findOrdinal b u keys) ids).result.map
        (fun p=>CodeGate.clause p (copyBytes (List.ofFn signs)).result)=
        some (.clause (List.ofFn (fun j=>word (slot j).val)) (List.ofFn signs))
      rw [H,A,copyBytes_exact]
      rfl
    · change (gatherOptions b (fun u=>findOrdinal b u keys) ids).steps+
        (copyBytes (List.ofFn signs)).steps+4≤currentGateFee w b N d
      rw [copyBytes_exact]
      simp only [List.length_ofFn,currentGateFee,Nat.mul_add] at C ⊢
      omega

#print axioms current_named_ordinal
#print axioms current_source_gate
end J6R50Leaf
