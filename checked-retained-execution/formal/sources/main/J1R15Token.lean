import J1R15Files
import J1R15BasisEval

/-! Metered MAIN token compilation. All indexing of the placement,
group-label, and candidate files is performed by sequential bit-address
lookup. The public files are the encodings of the actual source layout;
their one-time generation is a separate, not free, phase. -/
namespace J1R15
open AOracleMachineTime J1R14Query J1MainSourcePlacement MainProbe

def readMask (places groups candidate : File)
    (placeKey nodeKey groupKey : List Bool) : Meter Bool :=
  let p := lookup placeKey places
  match p.result with
  | none => ⟨false,p.steps+1⟩
  | some v =>
    let g := lookup (nodeKey++v) groups
    let a := lookup v candidate
    let ok := equalBits (g.result.getD []) groupKey
    let bit := match a.result with
      | some [b] => b
      | _ => false
    ⟨ok.result && bit,p.steps+g.steps+a.steps+ok.steps+nodeKey.length+v.length+5⟩


/-- Executable kernel; files and serialized fields arrive as tapes, so
their lookups and tensor products are evaluated rather than assumed. -/
def rawProduce (places groups candidate : File)
    (placeKey nodeKey groupKey : List Bool) (row : BasisRows) : Meter SignedUnit :=
  let m := readMask places groups candidate placeKey nodeKey groupKey
  let b := runBasis row
  let token := if m.result then b.result else SignedUnit.zero
  ⟨token,m.steps+b.steps+token.bits.length+1⟩

section Source
variable {q r n M h : ℕ} {E F A : Type*} [Fintype E]
variable (data : IncidenceData (Fin q) (Fin r) E (Fin n) F)
variable (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h)
variable (order : Fin M ≃ E)

noncomputable def readPlacedMask (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (c : Fin h) (u : Cell (Fin q) (Fin r)) : Meter Bool :=
  readMask (placedFile data cap order) (groupFile data.wordVar)
    (indexedCandidate (n:=n) (List.ofFn x)).result
    (positionCode (c,u)) (finWord t) (finWord g)

theorem readPlacedMask_exact (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (c : Fin h) (u : Cell (Fin q) (Fin r)) :
    (readPlacedMask data cap order x t g c u).result =
      (occupied data h cap c u).elim false (fun v => decide (data.wordVar v t = g) && x v) := by
  cases he : occupied data h cap c u with
  | none =>
    simp [readPlacedMask,readMask,placedFile_read,he]
  | some v =>
    simp only [readPlacedMask,readMask,placedFile_read,he,Option.map_some,Option.elim_some]
    change ((equalBits
      ((lookup (nodeVarCode t v) (groupFile data.wordVar)).result.getD []) (finWord g)).result &&
      (match (lookup (finWord v) (indexedCandidate (n:=n) (List.ofFn x)).result).result with
      | some [b] => b
      | _ => false)) = _
    rw [groupFile_read,indexedCandidate_read]
    simpa only [Option.getD_some] using congrArg (fun b => b && x v) (wordEq_result (data.wordVar v t) g)

def placeBudget (q r n M h : ℕ) : ℕ :=
  M*(5*(Nat.clog 2 h+2*q*Nat.clog 2 r)+Nat.clog 2 n+3)+1

def groupBudget (q r n : ℕ) : ℕ :=
  q*n*(5*(Nat.clog 2 q+Nat.clog 2 n)+Nat.clog 2 r+3)+1

def candidateBudget (n : ℕ) : ℕ := n*(5*Nat.clog 2 n+1+3)+1

def maskBudget (q r n M h : ℕ) : ℕ :=
  placeBudget q r n M h + groupBudget q r n + candidateBudget n +
    4*Nat.clog 2 r + Nat.clog 2 q + Nat.clog 2 n + 6

theorem readPlacedMask_cost (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (c : Fin h) (u : Cell (Fin q) (Fin r)) :
    (readPlacedMask data cap order x t g c u).steps ≤ maskBudget q r n M h := by
  have hp : (lookup (positionCode (c,u)) (placedFile data cap order)).steps ≤
      placeBudget q r n M h := placedFile_cost data cap order c u
  cases he : occupied data h cap c u with
  | none =>
    simp only [readPlacedMask,readMask,placedFile_read,he,Option.map_none]
    unfold maskBudget
    omega
  | some v =>
    simp only [readPlacedMask,readMask,placedFile_read,he,Option.map_some]
    change (lookup (positionCode (c,u)) (placedFile data cap order)).steps +
      (lookup (nodeVarCode t v) (groupFile data.wordVar)).steps +
      (lookup (finWord v) (indexedCandidate (n:=n) (List.ofFn x)).result).steps +
      (equalBits ((lookup (nodeVarCode t v) (groupFile data.wordVar)).result.getD []) (finWord g)).steps +
      (finWord t).length+(finWord v).length+5 ≤ _
    have hg : (lookup (nodeVarCode t v) (groupFile data.wordVar)).steps ≤
      groupBudget q r n := groupFile_cost data.wordVar t v
    have ha : (lookup (finWord v) (indexedCandidate (n:=n) (List.ofFn x)).result).steps ≤
      candidateBudget n := indexedCandidate_read_cost x v
    rw [groupFile_read,Option.getD_some,equalBits_cost,finWord_length,finWord_length,
      finWord_length,finWord_length,Nat.min_self]
    unfold maskBudget
    omega

/-- The producing computation starts from a public encoded basis row and
the non-token physical files. Its result is the actual signed contribution
of this occupied slot, possibly zero on the current Boolean candidate. -/
noncomputable def produceSlot (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (c : Fin h) (basis : Fin q → LocalBasis (Fin r)) (u : Cell (Fin q) (Fin r)) :
    Meter SignedUnit :=
  let m := readPlacedMask data cap order x t g c u
  let a := runBasis (fullBasisBits basis u)
  let token := if m.result then a.result else SignedUnit.zero
  ⟨token,m.steps+a.steps+token.bits.length+1⟩

theorem produceSlot_amount (pin : A → E) (hdiag : ∀ a, (data.cell (pin a)).1 = (data.cell (pin a)).2)
    (interval : Finset ℕ) (hzero : 0 ∉ interval)
    (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (c : Fin h) (basis : Exceptional (Fin q) (Fin r) interval) (u : Cell (Fin q) (Fin r)) :
    (produceSlot data cap order x t g c basis.val u).result.amount =
      slotAmount (sourceLayout data h cap pin hdiag) interval hzero t g (c,basis) x u := by
  classical
  dsimp only [produceSlot,slotAmount]
  rw [readPlacedMask_exact]
  change (if (occupied data h cap c u).elim false
    (fun v => decide (data.wordVar v t = g) && x v) then
      (runBasis (fullBasisBits basis.val u)).result else SignedUnit.zero).amount =
    basisEntry basis.val u * (occupied data h cap c u).elim 0
      (fun v => if data.wordVar v t = g ∧ x v = true then 1 else 0)
  cases he : occupied data h cap c u with
  | none => simp [SignedUnit.amount]
  | some v =>
    by_cases hg : data.wordVar v t = g
    · cases hx : x v
      · simp [hg,hx,SignedUnit.amount]
      · simpa [hg,hx] using fullBasis_exact basis.val u
    · simp [hg,SignedUnit.amount]

theorem produceSlot_cost (x : Fin n → Bool) (t : Fin q) (g : Fin r) (c : Fin h)
    (basis : Fin q → LocalBasis (Fin r)) (u : Cell (Fin q) (Fin r)) :
    (produceSlot data cap order x t g c basis u).steps ≤
      maskBudget q r n M h + (q*(16*Nat.clog 2 r+12+3)+1) + 3 := by
  have hm := readPlacedMask_cost data cap order x t g c u
  have hb := fullBasis_cost basis u
  dsimp only [produceSlot]
  rw [SignedUnit.bits_length]
  omega

theorem produceSlot_raw (x : Fin n → Bool) (t : Fin q) (g : Fin r)
    (c : Fin h) (basis : Fin q → LocalBasis (Fin r)) (u : Cell (Fin q) (Fin r)) :
    produceSlot data cap order x t g c basis u =
      rawProduce (placedFile data cap order) (groupFile data.wordVar)
        (indexedCandidate (n:=n) (List.ofFn x)).result (positionCode (c,u))
        (finWord t) (finWord g) (fullBasisBits basis u) := rfl

end Source

#print axioms readPlacedMask_exact
#print axioms readPlacedMask_cost
#print axioms produceSlot_amount
#print axioms produceSlot_cost
#print axioms produceSlot_raw
end J1R15
