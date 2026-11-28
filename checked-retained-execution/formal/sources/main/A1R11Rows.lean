import A1R11Packed

/-! Executable selection: immutable full option tape per row and one
shared moment tape. Both seeks pay for payloads actually crossed;
the output row-factor tape is generated from the raw assignment. -/

namespace A1R11
open A1R10 A1R9 AOracleMachineTime AOracleMachineTimeTape AOracleWitness AOracleSuccinct

theorem seekMenu_exact {A : Type*} {n b : ℕ} (data : Fin n → A) (a : Fin n)
    (payload : A → ℕ) (cap : ℕ) (hcap : ∀ j,payload (data j)≤cap) (fit : n≤2^b) :
    let w := seekBlock payload (encodeBits b a.val) (List.ofFn data)
    w.result=some (data a) ∧ w.steps≤(10*b+4+cap)*n := by
  obtain ⟨hr,hc⟩ := seekBlock_exact payload (encodeBits b a.val) (List.ofFn data)
  constructor
  · rw [hr,encodeBits_exact _ _ (a.isLt.trans_le fit),List.getElem?_ofFn]
    simp [a.isLt]
  · have hh := sum_map_le_length (List.ofFn data) payload cap (by
      intro x hx
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact hcap j)
    rw [encodeBits_length,List.length_ofFn] at hc
    rw [List.length_ofFn,Nat.mul_comm n cap] at hh
    rw [Nat.add_mul]
    omega

def rowChoiceBudget (m b c bc s e ell p : ℕ) (hp : 0<p) : ℕ :=
  (10*b+4+(s*(bc+uvWidth e ell p+2)+uvWidth e ell p+3))*(m+1)+
  (10*b+4+(s*(bc+uvWidth e ell p+2)+2))*(m+1)+
  pickComputeBudget s c bc e ell p hp+uvWidth e ell p+8

def runRow {p c bc ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : List Bool) (y : Bool) (addr : List Bool)
    (picks : List (Pick c bc f ell)) (moms : List (WireTape c bc f ell)) :
    Meter (UVBlock f ell) :=
  let a := seekBlock Pick.payload addr picks
  let b := seekBlock momentPayload addr moms
  let r := a.result.elim (⟨uvZero hp f ell,uvWidth f.length ell p⟩ : Meter (UVBlock f ell))
    (runPick hp he hv x y (b.result.getD []))
  ⟨r.result,a.steps+b.steps+r.steps+8⟩

theorem runRow_exact {p r c m delta bc ell b : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (P : Packed r c m delta bc f ell) (w : Witness r c m) (j : Fin r) (fit : m+1≤2^b)
    (s : ℕ) (hl : ∀ j,(P.localRecipe j).length≤s) (hm : ∀ k,(P.moment k).length≤s) :
    let a := w.2.2 j
    let v := runRow hp he hv (List.ofFn w.2.1) (w.1 j) (encodeBits b a.val) (P.rowTape j) P.momentTape
    uvRead hp f ell v.result=evaluateRow (P.denote hp) w j ∧
      v.steps≤rowChoiceBudget m b c bc s f.length ell p hp := by
  let slot := w.2.2 j
  let a := seekBlock Pick.payload (encodeBits b slot.val) (P.rowTape j)
  let bq := seekBlock momentPayload (encodeBits b slot.val) P.momentTape
  obtain ⟨ah,ac⟩ := seekMenu_exact (P.atChoice j) slot Pick.payload
    (s*(bc+uvWidth f.length ell p+2)+uvWidth f.length ell p+3) (by
      intro i
      unfold Packed.atChoice
      cases h : choice i with
      | none =>
        have hh := Nat.mul_le_mul_right (bc+uvWidth f.length ell p+2) (hl j)
        simp only [Pick.payload]
        omega
      | some k =>
        simp only [Pick.payload]
        omega) fit
  obtain ⟨bh,bcost⟩ := seekMenu_exact P.atMoment slot momentPayload
    (s*(bc+uvWidth f.length ell p+2)+2) (by
      intro i
      unfold Packed.atMoment
      cases h : choice i with
      | none => simp [momentPayload]
      | some k =>
        simp only [Option.elim_some,momentPayload,Nat.add_le_add_iff_right]
        exact Nat.mul_le_mul_right _ (hm k)) fit
  change a.result=_ at ah
  change a.steps≤_ at ac
  change bq.result=_ at bh
  change bq.steps≤_ at bcost
  let t := runPick hp he hv (List.ofFn w.2.1) (w.1 j) (P.atMoment slot) (P.atChoice j slot)
  obtain ⟨th,tc⟩ := runPick_exact hp he hv P w j s hl hm
  change uvRead hp f ell t.result=_ at th
  change t.steps≤_ at tc
  unfold runRow
  dsimp only
  change uvRead hp f ell (a.result.elim _ (runPick hp he hv (List.ofFn w.2.1) (w.1 j)
      (bq.result.getD []))).result=_ ∧
    a.steps+bq.steps+(a.result.elim _ (runPick hp he hv (List.ofFn w.2.1) (w.1 j)
      (bq.result.getD []))).steps+8≤_
  rw [ah,bh,Option.elim_some,Option.getD_some]
  refine ⟨th,?_⟩
  change a.steps+bq.steps+t.steps+8≤_
  unfold rowChoiceBudget
  omega

def runRows {p c bc ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : List Bool) (moms : List (WireTape c bc f ell)) :
    List Bool → List (List Bool) → List (List (Pick c bc f ell)) → Meter (List (UVBlock f ell))
  | [],[],[] => ⟨[],0⟩
  | y::ys,a::as,s::ss =>
    let q := runRow hp he hv x y a s moms
    let t := runRows hp he hv x moms ys as ss
    ⟨q.result::t.result,q.steps+t.steps+uvWidth f.length ell p+4⟩
  | _,_,_ => ⟨[],2⟩

def rowBudget (m b c bc s e ell p : ℕ) (hp : 0<p) : ℕ :=
  rowChoiceBudget m b c bc s e ell p hp+uvWidth e ell p+4

theorem runRows_exact {p r c m delta bc ell b : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (P : Packed r c m delta bc f ell) (w : Witness r c m) (fit : m+1≤2^b)
    (s : ℕ) (hl : ∀ j,(P.localRecipe j).length≤s) (hm : ∀ k,(P.moment k).length≤s) (js : List (Fin r)) :
    let q := runRows hp he hv (List.ofFn w.2.1) P.momentTape
      (js.map w.1) (js.map fun j => encodeBits b (w.2.2 j).val) (js.map P.rowTape)
    q.result.length=js.length ∧
    q.result.map (uvRead hp f ell)=js.map (evaluateRow (P.denote hp) w) ∧
    q.steps≤js.length*rowBudget m b c bc s f.length ell p hp := by
  induction js with
  | nil => simp [runRows]
  | cons j js ih =>
    let q := runRow hp he hv (List.ofFn w.2.1) (w.1 j)
      (encodeBits b (w.2.2 j).val) (P.rowTape j) P.momentTape
    let t := runRows hp he hv (List.ofFn w.2.1) P.momentTape
      (js.map w.1) (js.map fun k => encodeBits b (w.2.2 k).val) (js.map P.rowTape)
    obtain ⟨qh,qc⟩ := runRow_exact hp he hv P w j fit s hl hm
    obtain ⟨tl,th,tc⟩ := ih
    change uvRead hp f ell q.result=_ at qh
    change q.steps≤_ at qc
    change t.result.length=_ at tl
    change t.result.map (uvRead hp f ell)=_ at th
    change t.steps≤_ at tc
    refine ⟨?_,?_,?_⟩
    · change t.result.length+1=js.length+1
      rw [tl]
    · change uvRead hp f ell q.result :: t.result.map (uvRead hp f ell) =
        evaluateRow (P.denote hp) w j :: js.map (evaluateRow (P.denote hp) w)
      rw [qh,th]
    · change q.steps+t.steps+uvWidth f.length ell p+4≤(js.length+1)*_
      rw [Nat.succ_mul js.length]
      unfold rowBudget at tc ⊢
      omega

#print axioms seekMenu_exact
#print axioms runRow_exact
#print axioms runRows_exact
end A1R11

