import J6R19RetainedWords
import J6R15ModeCostCursor
import J6R21AncestorHistory

/-! The original Gate seed is a fixed-width suffix. A retained literal
body may begin with any number of zeros, including zeros already in the
true seed. Use two paid tape cursors, never sentinel-decode a Gate body. -/
namespace J6R53TerminalGate
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R19Retained
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000
set_option Elab.async false

def ahead : ℕ → List Bool → Meter (List Bool)
  | 0, xs => ⟨xs,2⟩
  | _+1, [] => ⟨[],2⟩
  | n+1, _::xs =>
    let r := ahead n xs
    ⟨r.result,r.steps+4⟩

def lag : List Bool → List Bool → Meter (List Bool)
  | xs, [] => ⟨xs,2⟩
  | [], _::_ => ⟨[],2⟩
  | _::xs, _::ys =>
    let r := lag xs ys
    ⟨r.result,r.steps+5⟩

theorem ahead_exact (w : ℕ) (xs : List Bool) :
    ahead w xs=⟨xs.drop w,2+4*min w xs.length⟩ := by
  induction w generalizing xs with
  | zero => simp [ahead]
  | succ d ih =>
    cases xs with
    | nil => simp [ahead]
    | cons x xs =>
      simp only [ahead,ih,List.drop_succ_cons,List.length_cons]
      congr 1
      omega

theorem lag_exact (xs ys : List Bool) :
    lag xs ys=⟨xs.drop ys.length,2+5*min xs.length ys.length⟩ := by
  induction ys generalizing xs with
  | nil => simp [lag]
  | cons y ys ih =>
    cases xs with
    | nil => simp [lag]
    | cons x xs =>
      simp only [lag,ih,List.drop_succ_cons,List.length_cons]
      congr 1
      omega

def suffix (w : ℕ) (body : List Bool) : Meter (Word w) :=
  let fast := ahead w body
  let tail := lag body fast.result
  let raw := scanWidth w tail.result
  ⟨⟨raw.result,(congrArg List.length (scanWidth_exact w tail.result).1).trans
    (A1R12.lowBits_len w tail.result)⟩,fast.steps+tail.steps+raw.steps+4⟩

private theorem scan_same_bits (xs : List Bool) :
    (scanWidth xs.length xs).result=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scanWidth,List.length_cons,ih]

theorem suffix_exact {w : ℕ} (headBits : List Bool) (seed : Word w) :
    suffix w (headBits++seed.bits)=⟨seed,9+8*w+5*headBits.length⟩ := by
  let xs := headBits++seed.bits
  have len : xs.length=headBits.length+w := by
    unfold xs
    rw [List.length_append,seed.size]
  have h : (xs.drop w).length=headBits.length := by
    rw [List.length_drop,len]
    omega
  have r : xs.drop (xs.drop w).length=seed.bits := by
    rw [h]
    simp [xs]
  have hA : min w xs.length=w := min_eq_left (by omega)
  have hB : min xs.length (xs.drop w).length=headBits.length := by
    rw [h]
    exact min_eq_right (by omega)
  have a : (scanWidth w seed.bits).result=seed.bits :=
    (congrArg (fun n=>(scanWidth n seed.bits).result) seed.size).symm.trans (scan_same_bits seed.bits)
  have fee : (scanWidth w seed.bits).steps=4*w+1 := (scanWidth_exact w seed.bits).2
  have R : (suffix w xs).result.bits=seed.bits := by
    change (scanWidth w (lag xs (ahead w xs).result).result).result=_
    rw [ahead_exact]
    dsimp only
    rw [lag_exact]
    dsimp only
    rw [r]
    exact a
  have P : (suffix w xs).steps=9+8*w+5*headBits.length := by
    change (ahead w xs).steps+(lag xs (ahead w xs).result).steps+
      (scanWidth w (lag xs (ahead w xs).result).result).steps+4=_
    rw [ahead_exact]
    dsimp only
    rw [lag_exact]
    dsimp only
    rw [r,hA,hB,fee]
    omega
  have eq : (suffix w xs).result=seed := by
    generalize (suffix w xs).result=z at R ⊢
    cases z
    cases seed
    simp_all
  change suffix w xs=_
  calc
    suffix w xs=⟨(suffix w xs).result,(suffix w xs).steps⟩ := rfl
    _=⟨seed,9+8*w+5*headBits.length⟩ := congrArg₂ Meter.mk eq P

theorem actual_traced_gate_suffix {f : ℤ[X]} {ell w : ℕ}
    {root cur : Point f ell} (tr : Trace root cur)
    (seed : PortAt root→Word w) (port : PortAt cur) :
    suffix w (tr.literal (fun u=>(seed u).bits) port)=
      ⟨seed (tr.back port),9+8*w+5*tr.depth⟩ := by
  rw [tr.literal_exact,suffix_exact,List.length_replicate]

#print axioms ahead_exact
#print axioms lag_exact
#print axioms suffix_exact
#print axioms actual_traced_gate_suffix
end J6R53TerminalGate
