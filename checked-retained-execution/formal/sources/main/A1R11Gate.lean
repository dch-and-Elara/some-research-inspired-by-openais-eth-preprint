import A1R9Framing

/-! Bit framing, target legality and mode multiplicity in the A1
witness format, independent of the coefficient ring. Invalid fields
are rejected before arithmetic, using exactly the same gate on the
native double quotient as on the scalar lane. -/

namespace A1R11
open AOracleMachineTime AOracleMachineTimeTape AOracleSuccinct AOracleWitness A1R9

/-- Row-specific Boolean target tape. Option zero always exists. -/
def legalTape {r m : ℕ} (target : Fin r → Fin m → Bool) (j : Fin r) : List Bool :=
  List.ofFn fun a : Fin (m+1) => (choice a).elim true (target j)

def selectLegal (addr : List Bool) (t : List Bool) : Meter Bool :=
  let x := seekBlock (fun _ => 1) addr t
  ⟨x.result.getD false,x.steps+3⟩

def legalStepBudget (m b : ℕ) : ℕ := (10*b+5)*(m+1)+3

theorem selectLegal_exact {r m b : ℕ} (target : Fin r → Fin m → Bool)
    (a : Fin (m+1)) (j : Fin r) (fit : m+1≤2^b) :
    (selectLegal (encodeBits b a.val) (legalTape target j)).result=
      (choice a).elim true (target j) ∧
    (selectLegal (encodeBits b a.val) (legalTape target j)).steps≤legalStepBudget m b := by
  let t := legalTape target j
  let x := seekBlock (fun _ => 1) (encodeBits b a.val) t
  have hlen : t.length=m+1 := List.length_ofFn
  obtain ⟨hv,hc⟩ := seekBlock_exact (fun _ => 1) (encodeBits b a.val) t
  have he : x.result=some ((choice a).elim true (target j)) := by
    change x.result=_ at hv
    rw [hv,encodeBits_exact b _ (a.isLt.trans_le fit)]
    unfold t legalTape
    rw [List.getElem?_ofFn]
    simp [a.isLt]
  refine ⟨?_,?_⟩
  · change x.result.getD false=_
    rw [he,Option.getD_some]
  · change x.steps+3≤_
    change x.steps≤_ at hc
    have hs := sum_map_le_length t (fun _ => 1) 1 (fun _ _ => le_rfl)
    rw [hlen,Nat.mul_one] at hs
    rw [encodeBits_length,hlen] at hc
    unfold legalStepBudget
    rw [show (10*b+5)*(m+1)=(10*b+4)*(m+1)+(m+1) by ring]
    omega

def runLegal : List (List Bool) → List (List Bool) → Meter Bool
  | [],[] => ⟨true,0⟩
  | a::as,t::ts =>
    let x := selectLegal a t
    let y := runLegal as ts
    ⟨x.result && y.result,x.steps+y.steps+2⟩
  | _,_ => ⟨false,0⟩

theorem runLegal_list {r m b : ℕ} (target : Fin r → Fin m → Bool) (a : Allocation r m)
    (fit : m+1≤2^b) (js : List (Fin r)) :
    let q := runLegal (js.map fun j => encodeBits b (a j).val) (js.map (legalTape target))
    (q.result=true ↔ ∀ j∈js, (choice (a j)).elim true (target j)=true) ∧
    q.steps≤js.length*(legalStepBudget m b+2) := by
  induction js with
  | nil => simp [runLegal]
  | cons j js ih =>
    let y := runLegal (js.map (fun j => encodeBits b (a j).val)) (js.map (legalTape target))
    obtain ⟨hv,hc⟩ := selectLegal_exact target (a j) j fit
    change (y.result=true ↔ _) ∧ y.steps≤_ at ih
    constructor
    · simp [runLegal,hv,ih.1,y]
    · change (selectLegal (encodeBits b (a j).val) (legalTape target j)).steps+y.steps+2≤_
      rw [List.length_cons,Nat.succ_mul js.length]
      omega

def runGate {r c m b : ℕ} (q : ℕ) (target : Fin r → Fin m → Bool)
    (beta : Fin m →₀ ℕ) (z : Code r c b) : Meter Bool :=
  let f := frameCode m z
  if f.result then
    let y := runLegal (rawChoices z) (List.ofFn (legalTape target))
    let u := checkMultiplicity b q beta (rawChoices z)
    ⟨y.result && u.result, f.steps+y.steps+u.steps+5⟩
  else ⟨false,f.steps+5⟩

def gateBudget (r m b q : ℕ) : ℕ :=
  r*(12*(b+1)+4)+r*(legalStepBudget m b+2)+m*(counterBudget r b q+2)+5

theorem runGate_exact {R : Type*} [CommRing R] {r c m b : ℕ}
    (S : RootTerms r c m R) (q : ℕ) (hq : 0<q) (beta : Fin m →₀ ℕ) (fit : m+1≤2^b)
    (hr : r<2^q) (hb : ∀ k, beta k<2^q) (z : Code r c b) :
    (runGate q S.isTarget beta z).result=(parse z).elim false (valid S beta) ∧
      (runGate q S.isTarget beta z).steps≤gateBudget r m b q := by
  let f := frameCode m z
  obtain ⟨hf,ht⟩ := frameCode_exact m fit z
  change (f.result=true ↔ _) at hf
  change f.steps=_ at ht
  unfold runGate
  dsimp only
  change (if f.result then _ else _ : Meter Bool).result=_ ∧
    (if f.result then _ else _ : Meter Bool).steps≤_
  cases hz : parse z with
  | none =>
    have hn : f.result=false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      have hfit := hf.mp hh
      simp [parse,hfit] at hz
    simp only [hn,Bool.false_eq_true,if_false,Option.elim_none,true_and]
    change f.steps+5≤gateBudget r m b q
    rw [ht]
    unfold gateBudget
    omega
  | some w =>
    have hcode : z=encode fit w := (parse_exact fit z w).mp hz
    have hy : f.result=true := hf.mpr (by rw [hcode]; exact fun j => (w.2.2 j).isLt)
    have hraw : rawChoices z=allocationWords b w.2.2 := by rw [hcode]; rfl
    have hl := runLegal_list S.isTarget w.2.2 fit (List.finRange r)
    have hrows : (List.finRange r).map (legalTape S.isTarget)=List.ofFn (legalTape S.isTarget) := by
      simp [List.finRange,Function.comp_def]
    have halloc : ((List.finRange r).map (fun j => encodeBits b (w.2.2 j).val))=
        allocationWords b w.2.2 := by simp [List.finRange,allocationWords,Function.comp_def]
    rw [hrows,halloc,List.length_finRange] at hl
    obtain ⟨hleg,hlc⟩ := hl
    obtain ⟨hmode,hcost⟩ := checkMultiplicity_exact w.2.2 beta b q hq fit hr hb
    rw [if_pos hy,Option.elim_some,hraw]
    constructor
    · apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true,hleg,hmode,valid,decide_eq_true_eq,legal,allowed,
        List.mem_finRange,true_implies]
      tauto
    · change f.steps+(runLegal (allocationWords b w.2.2) (List.ofFn (legalTape S.isTarget))).steps+
        (checkMultiplicity b q beta (allocationWords b w.2.2)).steps+5≤_
      rw [ht]
      unfold gateBudget
      omega

#print axioms selectLegal_exact
#print axioms runLegal_list
#print axioms runGate_exact
end A1R11

