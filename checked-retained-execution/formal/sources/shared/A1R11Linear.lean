import A1R10Ops
import A1R9Scalar

/-! Fixed-width packed sparse UV linear forms. The target index is
decoded only in the correctness proof; the executable kernel walks
the Boolean assignment tape with the literal address and accumulates
the selected coefficients with the verified UV adder. -/

namespace A1R11
open A1R10 A1R9 AOracleMachineTime AOracleMachineTimeTape AOracleSuccinct

structure Wire {p : ℕ} (c bc : ℕ) (f : List (A1R10.Word p)) (ell : ℕ) where
  addr : A1R10.Word bc
  coeff : UVBlock f ell
  inRange : bitsValue addr.val < c

def Wire.position {p c bc ell : ℕ} {f : List (A1R10.Word p)}
    (w : Wire c bc f ell) : Fin c := ⟨bitsValue w.addr.val,w.inRange⟩

def packWire {p c bc ell : ℕ} {f : List (A1R10.Word p)} (fit : c≤2^bc)
    (j : Fin c) (z : UVBlock f ell) : Wire c bc f ell :=
  ⟨⟨encodeBits bc j.val,encodeBits_length _ _⟩,z,by
    rw [encodeBits_exact _ _ (j.isLt.trans_le fit)]
    exact j.isLt⟩

theorem packWire_position {p c bc ell : ℕ} {f : List (A1R10.Word p)} (fit : c≤2^bc)
    (j : Fin c) (z : UVBlock f ell) : (packWire fit j z).position=j := by
  apply Fin.ext
  exact encodeBits_exact _ _ (j.isLt.trans_le fit)

noncomputable def linearDenote {p c bc ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (ts : List (Wire c bc f ell)) :=
  ts.map fun w => (w.position,uvRead hp f ell w.coeff)

def uvWidth (e ell p : ℕ) : ℕ := ell*(e*p+1)+4

def linearStepBudget (c bc e ell p : ℕ) (hp : 0<p) : ℕ :=
  (10*bc+5)*c+ell*(uBudgetGates e p hp+4*(e*p+1))+bc+uvWidth e ell p+6

def linearBudget (s c bc e ell p : ℕ) (hp : 0<p) : ℕ :=
  uvWidth e ell p+s*linearStepBudget c bc e ell p hp

/-- Sequential traversal only. Crossing the coefficient payload is
charged even on a disabled port. -/
def runUVLinear {p c bc ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)} (x : List Bool) :
    List (Wire c bc f ell) → Meter (UVBlock f ell)
  | [] => ⟨uvZero hp f ell,uvWidth f.length ell p⟩
  | a::as =>
    let h := seekBlock (fun _ => 1) a.addr.val x
    let t := runUVLinear hp x as
    let u := if h.result.getD false then uvAdd hp a.coeff t.result else Meter.pure t.result
    ⟨u.result,h.steps+t.steps+u.steps+bc+uvWidth f.length ell p+6⟩

theorem runUVLinear_exact {p c bc ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (x : Fin c → Bool) (ts : List (Wire c bc f ell)) :
    uvRead hp f ell (runUVLinear hp (List.ofFn x) ts).result=
      linearEval x (linearDenote hp ts) ∧
    (runUVLinear hp (List.ofFn x) ts).steps≤linearBudget ts.length c bc f.length ell p hp := by
  induction ts with
  | nil => simp [runUVLinear,linearBudget,linearEval,linearDenote]
  | cons a as ih =>
    let v := seekBlock (fun _ => 1) a.addr.val (List.ofFn x)
    let t := runUVLinear hp (List.ofFn x) as
    have hx := seekBlock_exact (fun _ => 1) a.addr.val (List.ofFn x)
    obtain ⟨ha,hc⟩ := hx
    have hread : v.result=some (x a.position) := by
      change v.result=_ at ha
      rw [ha,List.getElem?_ofFn]
      simp [Wire.position,a.inRange]
    have hseek : v.steps≤(10*bc+5)*c := by
      change v.steps≤_ at hc
      have hs := sum_map_le_length (List.ofFn x) (fun _ => 1) 1 (fun _ _ => le_rfl)
      rw [a.addr.property,List.length_ofFn] at hc
      rw [List.length_ofFn,Nat.mul_one] at hs
      rw [show (10*bc+5)*c=(10*bc+4)*c+c by ring]
      omega
    obtain ⟨htv,htc⟩ := ih
    change uvRead hp f ell t.result=_ at htv
    change t.steps≤_ at htc
    let q := uvAdd hp a.coeff t.result
    obtain ⟨hqv,hqc⟩ := uvAdd_exact hp a.coeff t.result
    change uvRead hp f ell q.result=_ at hqv
    change q.steps≤_ at hqc
    let u := if v.result.getD false then q else Meter.pure t.result
    change uvRead hp f ell u.result=_ ∧
      v.steps+t.steps+u.steps+bc+uvWidth f.length ell p+6≤_
    have huc : u.steps≤ell*(uBudgetGates f.length p hp+4*(f.length*p+1)) := by
      unfold u
      split
      · exact hqc
      · exact Nat.zero_le _
    constructor
    · simp only [u,hread,Option.getD_some,linearDenote,List.map_cons,linearEval]
      change uvRead hp f ell (if x a.position then q else Meter.pure t.result).result =
        (if x a.position then uvRead hp f ell a.coeff else 0)+linearEval x (linearDenote hp as)
      cases h : x a.position
      · simpa only [h,Bool.false_eq_true,if_false,zero_add] using htv
      · simpa only [h,if_true,htv] using hqv
    · simp only [linearBudget,List.length_cons,Nat.succ_mul as.length]
      unfold linearBudget at htc
      unfold linearStepBudget at htc ⊢
      omega

#print axioms packWire_position
#print axioms runUVLinear_exact
end A1R11

