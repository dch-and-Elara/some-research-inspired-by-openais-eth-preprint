import A1R11Linear

/-! Assignment-independent normalized coefficient records: one local
list per row, one crossing cell per row/option, and one source-moment
list per mode, not one duplicated list per row/mode/assignment. -/

namespace A1R11
open A1R10 AOracleMachineTime AOracleMachineTimeTape AOracleSuccinct AOracleWitness

abbrev WireTape {p : ℕ} (c bc : ℕ) (f : List (A1R10.Word p)) (ell : ℕ) :=
  List (Wire c bc f ell)

structure Packed {p : ℕ} (r c m delta bc : ℕ) (f : List (A1R10.Word p)) (ell : ℕ) where
  rows : List (BoolTensor r delta)
  cols : List (BoolTensor c delta)
  localRecipe : Fin r → WireTape c bc f ell
  cross : Fin r → Fin m → UVBlock f ell
  target : Fin r → Fin m → Bool
  moment : Fin m → WireTape c bc f ell

noncomputable def Packed.denote {p r c m delta bc ell : ℕ} {f : List (A1R10.Word p)}
    (hp : 0<p) (P : Packed r c m delta bc f ell) :
    Recipes (AOracleCoordinates.Truncated (Modulus p hp f) ell) r c m delta where
  rows := P.rows
  cols := P.cols
  localRecipe j := linearDenote hp (P.localRecipe j)
  cross j k := uvRead hp f ell (P.cross j k)
  target := P.target
  moment k := linearDenote hp (P.moment k)

inductive Pick {p : ℕ} (c bc : ℕ) (f : List (A1R10.Word p)) (ell : ℕ) where
  | local (recipe : WireTape c bc f ell)
  | mode (target : Bool) (cross : UVBlock f ell)

def Pick.payload {p c bc ell : ℕ} {f : List (A1R10.Word p)} : Pick c bc f ell → ℕ
  | .local a => a.length*(bc+uvWidth f.length ell p+2)+2
  | .mode _ _ => uvWidth f.length ell p+3

def Packed.atChoice {p r c m delta bc ell : ℕ} {f : List (A1R10.Word p)}
    (P : Packed r c m delta bc f ell) (j : Fin r) (a : Fin (m+1)) : Pick c bc f ell :=
  match choice a with
  | none => .local (P.localRecipe j)
  | some k => .mode (P.target j k) (P.cross j k)

def Packed.rowTape {p r c m delta bc ell : ℕ} {f : List (A1R10.Word p)}
    (P : Packed r c m delta bc f ell) (j : Fin r) : List (Pick c bc f ell) :=
  List.ofFn (P.atChoice j)

def Packed.atMoment {p r c m delta bc ell : ℕ} {f : List (A1R10.Word p)}
    (P : Packed r c m delta bc f ell) (a : Fin (m+1)) : WireTape c bc f ell :=
  (choice a).elim [] P.moment

def Packed.momentTape {p r c m delta bc ell : ℕ} {f : List (A1R10.Word p)}
    (P : Packed r c m delta bc f ell) : List (WireTape c bc f ell) :=
  List.ofFn P.atMoment

def momentPayload {p c bc ell : ℕ} {f : List (A1R10.Word p)} (w : WireTape c bc f ell) : ℕ :=
  w.length*(bc+uvWidth f.length ell p+2)+2

def signBudget (e ell p : ℕ) (hp : 0<p) : ℕ :=
  ell*(2*uBudgetGates e p hp+4*(e*p+1))+uvWidth e ell p+4

def uvSign {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (y nonzero : Bool) (a : UVBlock f ell) :
    Meter (UVBlock f ell) :=
  if y then ⟨a,4⟩ else
    let c := if nonzero then uvZero hp f ell else uvOne hp he hv
    let u := uvSub hp he c a
    ⟨u.result,u.steps+uvWidth f.length ell p+4⟩

theorem uvSign_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (y nonzero : Bool) (a : UVBlock f ell) :
    uvRead hp f ell (uvSign hp he hv y nonzero a).result =
      (if y then uvRead hp f ell a else
        (if nonzero then 0 else 1)-uvRead hp f ell a) ∧
    (uvSign hp he hv y nonzero a).steps≤signBudget f.length ell p hp := by
  cases y
  · let c := if nonzero then uvZero hp f ell else uvOne hp he hv
    obtain ⟨hr,hc⟩ := uvSub_exact hp he c a
    refine ⟨?_,?_⟩
    · change uvRead hp f ell (uvSub hp he c a).result=_
      rw [hr]
      cases nonzero <;> simp [c]
    · change (uvSub hp he c a).steps+uvWidth f.length ell p+4≤_
      unfold signBudget
      omega
  · simp [uvSign,signBudget]

def pickComputeBudget (s c bc e ell p : ℕ) (hp : 0<p) : ℕ :=
  linearBudget s c bc e ell p hp+3432*((ell+1)^2*(e+1)^2*(p+1)^2)+
  signBudget e ell p hp+uvWidth e ell p+6

def runPick {p c bc ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (x : List Bool) (y : Bool)
    (mom : WireTape c bc f ell) : Pick c bc f ell → Meter (UVBlock f ell)
  | .local d =>
    let a := runUVLinear hp x d
    let b := uvSign hp he hv y false a.result
    ⟨b.result,a.steps+b.steps+6⟩
  | .mode legal cb =>
    if legal then
      let a := runUVLinear hp x mom
      let b := uvMul hp cb a.result
      let v := uvSign hp he hv y true b.result
      ⟨v.result,a.steps+b.steps+v.steps+6⟩
    else ⟨uvZero hp f ell,uvWidth f.length ell p+6⟩

theorem runPick_exact {p r c m delta bc ell : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell)
    (P : Packed r c m delta bc f ell) (w : Witness r c m) (j : Fin r)
    (s : ℕ) (hl : ∀ j,(P.localRecipe j).length≤s) (hm : ∀ k,(P.moment k).length≤s) :
    let a := w.2.2 j
    let v := runPick hp he hv (List.ofFn w.2.1) (w.1 j) (P.atMoment a) (P.atChoice j a)
    uvRead hp f ell v.result=evaluateRow (P.denote hp) w j ∧
    v.steps≤pickComputeBudget s c bc f.length ell p hp := by
  dsimp only
  unfold Packed.atMoment Packed.atChoice evaluateRow
  cases h : choice (w.2.2 j) with
  | none =>
    let a := runUVLinear hp (List.ofFn w.2.1) (P.localRecipe j)
    obtain ⟨ha,hac⟩ := runUVLinear_exact hp w.2.1 (P.localRecipe j)
    obtain ⟨hs,hsc⟩ := uvSign_exact hp he hv (w.1 j) false a.result
    change a.steps≤_ at hac
    have hb := Nat.mul_le_mul_right (linearStepBudget c bc f.length ell p hp) (hl j)
    constructor
    · change uvRead hp f ell (uvSign hp he hv (w.1 j) false a.result).result=_
      rw [hs,ha]
      rfl
    · change a.steps+(uvSign hp he hv (w.1 j) false a.result).steps+6≤_
      unfold pickComputeBudget
      unfold linearBudget at hac ⊢
      omega
  | some k =>
    cases hleg : P.target j k with
    | false =>
      have z : (P.denote hp).target j k=false := hleg
      simp [runPick,hleg,z,pickComputeBudget]
    | true =>
      let a := runUVLinear hp (List.ofFn w.2.1) (P.moment k)
      let b := uvMul hp (P.cross j k) a.result
      obtain ⟨ha,hac⟩ := runUVLinear_exact hp w.2.1 (P.moment k)
      obtain ⟨hb,hbc⟩ := uvMul_native_bit_cost hp (P.cross j k) a.result
      obtain ⟨hs,hsc⟩ := uvSign_exact hp he hv (w.1 j) true b.result
      change a.steps≤_ at hac
      change b.steps≤_ at hbc
      have hsize := Nat.mul_le_mul_right (linearStepBudget c bc f.length ell p hp) (hm k)
      have z : (P.denote hp).target j k=true := hleg
      simp only [Option.elim_some,hleg,z,if_true]
      constructor
      · change uvRead hp f ell (uvSign hp he hv (w.1 j) true b.result).result=_
        rw [hs,show uvRead hp f ell b.result=_ from hb,ha]
        rfl
      · change a.steps+b.steps+(uvSign hp he hv (w.1 j) true b.result).steps+6≤_
        unfold pickComputeBudget
        unfold linearBudget at hac ⊢
        omega

#print axioms uvSign_exact
#print axioms runPick_exact
end A1R11


