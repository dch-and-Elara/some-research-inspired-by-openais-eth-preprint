import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! A4 source-scale arithmetic: fill every ordered word cell to one
uniform exact load, retaining the printed logarithm and leaving room
in the diagonal cell for all prescribed hard row/column pairs. -/
namespace A4R45PrintedLoad
set_option autoImplicit false
set_option warningAsError true

def scale (m : ℕ) : ℕ := 2*Nat.clog 2 (m+2)
def bits (ell den : ℕ) : ℕ := 2*(ell/den)
def wireCount (ell : ℕ) : ℕ := 2^ell
def wordCells (a : ℕ) : ℕ := 64^(2*a)
def cellLoad (ell a : ℕ) : ℕ := 2^(ell-12*a)
def packetCopies (ell a : ℕ) : ℕ := 2^(ell-13*a)

theorem word_cells_pow_two (a : ℕ) : wordCells a=2^(12*a) := by
  unfold wordCells
  rw [show (64:ℕ)=2^6 by decide, ←pow_mul]
  congr 1
  omega

theorem loaded_all_cells (ell a : ℕ) (h : 13*a≤ell) :
    wordCells a*cellLoad ell a=wireCount ell ∧
      packetCopies ell a * 2^a=cellLoad ell a := by
  constructor
  · rw [word_cells_pow_two,cellLoad,wireCount,←pow_add]
    congr 1
    omega
  · rw [packetCopies,cellLoad,←pow_add]
    congr 1
    omega

theorem printed_square_growth (m : ℕ) :
    (m+2)^2≤wireCount (scale m) ∧ wireCount (scale m) < (2*(m+2))^2 := by
  let c := Nat.clog 2 (m+2)
  have hc : 0<c := Nat.clog_pos (by decide) (by omega)
  have hlo : m+2≤2^c := Nat.le_pow_clog (by decide) _
  have hh : 2^(c-1)<m+2 := Nat.pow_pred_clog_lt_self (by decide) (by omega)
  have h2 : 2^c=2*2^(c-1) := by
    calc
      _ = 2^((c-1)+1) := congrArg (fun i : ℕ => 2^i) (Nat.sub_add_cancel hc).symm
      _ = _ := by rw [pow_succ']
  have hhi : 2^c<2*(m+2) := by rw [h2]; omega
  change _≤2^(2*c) ∧ 2^(2*c)<_
  rw [Nat.mul_comm 2 c, pow_mul]
  exact ⟨Nat.pow_le_pow_left hlo _,Nat.pow_lt_pow_left hhi (by decide)⟩

theorem padded_clog_unchanged (m δ : ℕ) (hδ : δ≤m) :
    Nat.clog 2 (wireCount (scale m) - δ)=scale m := by
  let ell := scale m
  have pos : 0<ell := by
    unfold ell scale
    have : 0<Nat.clog 2 (m+2) := Nat.clog_pos (by decide) (by omega)
    omega
  have hpow : wireCount ell=2*2^(ell-1) := by
    unfold wireCount
    calc
      _ = 2^((ell-1)+1) := congrArg (fun i : ℕ => 2^i) (Nat.sub_add_cancel pos).symm
      _ = _ := by rw [pow_succ']
  have hm : 2*m < wireCount ell :=
    lt_of_lt_of_le (by nlinarith) (printed_square_growth m).1
  have hstrict : 2^(ell-1)<wireCount ell-δ := by omega
  have hlo := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2 hstrict
  have hhi : Nat.clog 2 (wireCount ell-δ)≤ell :=
    (Nat.clog_le_iff_le_pow (by decide)).2 (Nat.sub_le _ _)
  change Nat.clog 2 (wireCount ell-δ)=ell
  omega

theorem printed_diagonal_room (m den : ℕ) (largeDen : 48≤den)
    (nonzeroLevel : den ≤ scale m) :
    let ell:=scale m
    let a:=bits ell den
    0<a ∧ 13*a<ell ∧ m ≤ cellLoad ell a ∧
       wordCells a * cellLoad ell a = wireCount ell ∧
       packetCopies ell a * 2^a = cellLoad ell a := by
  dsimp only
  let c := Nat.clog 2 (m+2)
  let ell := 2*c
  let q := ell/den
  change 0<2*q ∧ 13*(2*q)<ell ∧ m≤2^(ell-12*(2*q)) ∧ _
  have qpos : 0<q := Nat.div_pos nonzeroLevel (by omega)
  have hb : 48*q≤ell := calc
    _ ≤ den*q := Nat.mul_le_mul_right q largeDen
    _ = q*den := Nat.mul_comm _ _
    _ ≤ _ := Nat.div_mul_le_self _ _
  have hx : 13*(2*q)<ell := by omega
  have hclog : m+2≤2^c := Nat.le_pow_clog (by decide) _
  have hstep : c≤ell-12*(2*q) := by dsimp only [ell] at hb ⊢; omega
  have hf : m≤2^(ell-12*(2*q)) :=
    (Nat.le_add_right _ _).trans (hclog.trans (Nat.pow_le_pow_right (by decide) hstep))
  exact ⟨by omega,hx,hf,loaded_all_cells ell (2*q) hx.le⟩

theorem hard_pairs_fit (k ell a : ℕ) (ha : 0<a) (hm : 13*a≤ell)
    (unpacked : 6*k≤cellLoad ell a) :
    2*k ≤ packetCopies ell a * 2^(a-1) := by
  have hl : (2:ℕ)^a=2*2^(a-1) := by
    calc
      _ = 2^((a-1)+1) := congrArg (fun i : ℕ => (2:ℕ)^i) (Nat.sub_add_cancel ha).symm
      _ = _ := by rw [pow_succ']
  have pack := (loaded_all_cells ell a hm).2
  rw [hl, ←Nat.mul_assoc, Nat.mul_comm (packetCopies ell a) 2, Nat.mul_assoc] at pack
  omega

#print axioms word_cells_pow_two
#print axioms loaded_all_cells
#print axioms printed_square_growth
#print axioms padded_clog_unchanged
#print axioms printed_diagonal_room
#print axioms hard_pairs_fit
end A4R45PrintedLoad
