import P3BareissBitBackward

namespace Paper3.BareissBit

open Reconstruction.BareissSolver Reconstruction.BareissPaper
open AffineCost.Bit (Run)

def headerDebit (m n nav : ℕ) : ℕ := (m*n+m+n+8)*nav

def branchCap (m n B nav : ℕ) : ℕ :=
  let c := cellPrice B+nav
  headerDebit m n nav + (m*n+1)*c + (m+1)*c + (4*m*(n+1)+1)*c + (3*n+6)*c

theorem branchCap_mono {m n m' n' B B' nav nav' : ℕ}
    (hm : m ≤ m') (hn : n ≤ n') (hb : B ≤ B') (hv : nav ≤ nav') :
    branchCap m n B nav ≤ branchCap m' n' B' nav' := by
  unfold branchCap headerDebit cellPrice scalarBudget
  dsimp only
  gcongr

def paidPivot {m n : ℕ} (B nav : ℕ) (M : IntegerAugment m n) :
    Run (Scan (Fin m × Fin n)) :=
  paidScan B nav (fun ij => M ij.1 (some ij.2)) (candidates m n)

def paidRhs {m n : ℕ} (B nav : ℕ) (M : IntegerAugment m n) :
    Run (Scan (Fin m)) :=
  paidScan B nav (fun i => M i none) (List.finRange m)

theorem paidPivot_correct {m n : ℕ} (B nav : ℕ) (M : IntegerAugment m n)
    (h : ValidTrace B (pivotTrace M)) : (paidPivot B nav M).value = pivotScan M :=
  paidScan_correct _ _ _ _ h

theorem paidRhs_correct {m n : ℕ} (B nav : ℕ) (M : IntegerAugment m n)
    (h : ValidTrace B (zeroTrace M)) : (paidRhs B nav M).value = rhsScan M :=
  paidScan_correct _ _ _ _ h

theorem paidPivot_price {m n : ℕ} (B nav : ℕ) (M : IntegerAugment m n) :
    (paidPivot B nav M).steps ≤ (m*n+1)*(cellPrice B+nav) := by
  simpa only [paidPivot,candidates_length] using
    paidScan_price B nav (fun (ij : Fin m × Fin n) => M ij.1 (some ij.2)) (candidates m n)

theorem paidRhs_price {m n : ℕ} (B nav : ℕ) (M : IntegerAugment m n) :
    (paidRhs B nav M).steps ≤ (m+1)*(cellPrice B+nav) := by
  simpa only [paidRhs,List.length_finRange] using
    paidScan_price B nav (fun i : Fin m => M i none) (List.finRange m)

/-- There is one controller recursion. It starts each reached frame with
its dimension/roster allowance. The *bit* test selects the next branch;
a selected frame consumes the forward bit results as its actual child
table and uses the returned solution in the paid backward arithmetic. -/
def paidRun (B nav : ℕ) :
    (m n : ℕ) → IntegerAugment m n → ℤ → Run (Option (ScaledSolution n))
  | 0, n, _, d => ⟨some ⟨d,0⟩,headerDebit 0 n nav⟩
  | m+1, 0, M, d =>
      let R := paidRhs B nav M
      ⟨zeroAnswer d R.value,headerDebit (m+1) 0 nav+R.steps⟩
  | m+1, n+1, M, d =>
      let P := paidPivot B nav M
      let time := headerDebit (m+1) (n+1) nav + P.steps
      match P.value.found with
      | none =>
        let R := paidRhs B nav M
        ⟨zeroAnswer d R.value,time+R.steps⟩
      | some (i,j) =>
        let F := paidForward B nav M d i j
        let child := paidRun B nav m n F.value (M i (some j))
        let now := time+F.steps+child.steps
        match child.value with
        | none => ⟨none,now⟩
        | some x =>
          let r := paidBackward B nav M i j x
          ⟨some r.value,now+r.steps⟩

theorem paidRun_correct (B nav m n : ℕ) (M : IntegerAugment m n) (d : ℤ)
    (h : ValidTrace B (arithmeticTrace m n M d)) :
    (paidRun B nav m n M d).value = (runInt m n M d).result := by
  induction m generalizing n d with
  | zero => rfl
  | succ m ih =>
    cases n with
    | zero =>
      have hx : ValidTrace B (zeroTrace M) := h
      simp only [paidRun,runInt,paidRhs_correct B nav M hx]
    | succ n =>
      have ha : ValidTrace B (pivotTrace M ++
          match integerPivot M with
          | none => zeroTrace M
          | some (i,j) =>
            let N := forwardStep M d i j
            let p := M i (some j)
            forwardTrace M d i j ++ arithmeticTrace m n N p ++
              (runInt m n N p).result.toList.flatMap (fun x => backwardTrace M i j x)) := h
      have hp := paidPivot_correct B nav M (valid_left ha)
      have ht := valid_right ha
      simp only [paidRun,runInt,hp]
      cases he : (pivotScan M).found with
      | none =>
        have hr : ValidTrace B (zeroTrace M) := by simpa only [integerPivot,he] using ht
        simp only [paidRhs_correct B nav M hr]
      | some p =>
        rcases p with ⟨i,j⟩
        let N := forwardStep M d i j
        let b := M i (some j)
        have hc : ValidTrace B
            ((forwardTrace M d i j ++ arithmeticTrace m n N b) ++
              (runInt m n N b).result.toList.flatMap (fun x => backwardTrace M i j x)) := by
          simpa only [integerPivot,he,N,b] using ht
        have hf := paidForward_correct B nav M d i j (valid_left (valid_left hc))
        have hchild := ih n N b (valid_right (valid_left hc))
        change (match (paidRun B nav m n (paidForward B nav M d i j).value b).value with
            | none => (⟨none, _⟩ : Run (Option (ScaledSolution (n+1))))
            | some x => ⟨some (paidBackward B nav M i j x).value, _⟩).value =
          (runInt m n N b).result.map (backwardStep M i j)
        rw [hf,hchild]
        cases hr : (runInt m n N b).result with
        | none => rfl
        | some x =>
          have hbx : ValidTrace B (backwardTrace M i j x) := by
            simpa only [hr,Option.toList_some,List.flatMap_cons,List.flatMap_nil,
              List.append_nil] using valid_right hc
          change some (paidBackward B nav M i j x).value = some (backwardStep M i j x)
          rw [paidBackward_correct B nav M i j x hbx]

theorem paidRun_price (B nav m n : ℕ) (M : IntegerAugment m n) (d : ℤ) :
    (paidRun B nav m n M d).steps ≤ (min m n+1)*branchCap m n B nav := by
  induction m generalizing n d with
  | zero =>
    simp only [paidRun,Nat.zero_min,Nat.zero_add,Nat.one_mul,branchCap]
    omega
  | succ m ih =>
    cases n with
    | zero =>
      have hr := paidRhs_price B nav M
      simp only [paidRun,Nat.min_zero,Nat.zero_add,Nat.one_mul,branchCap]
      omega
    | succ n =>
      let big := branchCap (m+1) (n+1) B nav
      let f := paidPivot B nav M
      have hp : f.steps ≤ ((m+1)*(n+1)+1)*(cellPrice B+nav) :=
        paidPivot_price B nav M
      have hbig : branchCap m n B nav ≤ big :=
        branchCap_mono (Nat.le_succ m) (Nat.le_succ n) le_rfl le_rfl
      have hmin : min (m+1) (n+1)+1 = min m n+1+1 := by omega
      simp only [paidRun,hmin]
      change (match f.value.found with
        | none => ⟨zeroAnswer d (paidRhs B nav M).value,
            headerDebit (m+1) (n+1) nav + f.steps + (paidRhs B nav M).steps⟩
        | some (i,j) =>
          let F := paidForward B nav M d i j
          let c := paidRun B nav m n F.value (M i (some j))
          match c.value with
          | none => ⟨none,headerDebit (m+1) (n+1) nav+f.steps+F.steps+c.steps⟩
          | some x => ⟨some (paidBackward B nav M i j x).value,
              headerDebit (m+1) (n+1) nav+f.steps+F.steps+c.steps+
                (paidBackward B nav M i j x).steps⟩
        : Run (Option (ScaledSolution (n+1)))).steps ≤ (min m n+1+1)*big
      cases hf : f.value.found with
      | none =>
        have hr := paidRhs_price B nav M
        have hh : headerDebit (m+1) (n+1) nav+f.steps+(paidRhs B nav M).steps ≤ big := by
          dsimp only [big,branchCap]
          omega
        exact hh.trans (Nat.le_mul_of_pos_left _ (by omega))
      | some p =>
        rcases p with ⟨i,j⟩
        let F := paidForward B nav M d i j
        let c := paidRun B nav m n F.value (M i (some j))
        have hc : c.steps ≤ (min m n+1)*big := by
          exact (ih n _ _).trans (Nat.mul_le_mul_left _ hbig)
        have hF : F.steps ≤ (4*(m+1)*(n+1+1)+1)*(cellPrice B+nav) :=
          (paidForward_price B nav M d i j).trans (by gcongr <;> omega)
        have hl : headerDebit (m+1) (n+1) nav+f.steps+F.steps ≤ big := by
          dsimp only [big,branchCap]
          omega
        simp only
        cases hh : c.value with
        | none =>
          change headerDebit (m+1) (n+1) nav+f.steps+F.steps+c.steps ≤ _
          rw [Nat.add_mul,Nat.one_mul]
          omega
        | some x =>
          have hx : (paidBackward B nav M i j x).steps ≤ (3*(n+1)+6)*(cellPrice B+nav) :=
            (paidBackward_price B nav M i j x).trans (by gcongr; omega)
          have hl' : headerDebit (m+1) (n+1) nav+f.steps+F.steps+
              (paidBackward B nav M i j x).steps ≤ big := by
            dsimp only [big,branchCap]
            omega
          change headerDebit (m+1) (n+1) nav+f.steps+F.steps+c.steps+
            (paidBackward B nav M i j x).steps ≤ _
          rw [Nat.add_mul,Nat.one_mul]
          omega

end Paper3.BareissBit

#print axioms Paper3.BareissBit.branchCap_mono
#print axioms Paper3.BareissBit.paidPivot_correct
#print axioms Paper3.BareissBit.paidRhs_correct
#print axioms Paper3.BareissBit.paidRun_correct
#print axioms Paper3.BareissBit.paidRun_price

