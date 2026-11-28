
import J6R24LegalLayoutMask
import J6R23PaddingCensusCodec

/-! Optional general packet conventions supplied as an explicit format
with one full page key and its bounded flag word per record. Lookups
are real, charged binary scans, not calls to a mask oracle. -/
namespace J6R24LegalLayout
open scoped Classical BigOperators
open P11FullPacking A1R10 AOracleMachineTime AOracleMachineTimeTape J6R23PaddingCensus
set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false

structure FlagRow (pageWidth : ℕ) where
  key : Word pageWidth
  flags : List Bool

def flagSearchFee (bw a : ℕ) := 16*bw+6*a+18

def flagSearch {bw : ℕ} (a : ℕ) (key : Word bw) :
    List (FlagRow bw)→Meter (Option (List Bool))
  | [] => ⟨none,4⟩
  | x::xs =>
    let z := A1R9.eqWord key.val x.key.val
    if z.result then ⟨some x.flags,z.steps+6*bw+6*a+18⟩
    else
      let rest := flagSearch a key xs
      ⟨rest.result,rest.steps+z.steps+6*bw+6*a+18⟩

theorem flag_search_cost {bw : ℕ} (a : ℕ) (key : Word bw) (xs : List (FlagRow bw)) :
    (flagSearch a key xs).steps≤4+xs.length*flagSearchFee bw a := by
  induction xs with
  | nil => simp [flagSearch]
  | cons x xs ih =>
    let Z := A1R9.eqWord key.val x.key.val
    have h : Z.steps=10*bw := by
      exact (A1R9.eqWord_exact key.val x.key.val (key.property.trans x.key.property.symm)).2.trans
        (congrArg (fun n=>10*n) key.property)
    change (if Z.result then (⟨some x.flags,Z.steps+6*bw+6*a+18⟩:Meter (Option (List Bool))) else
      ⟨(flagSearch a key xs).result,(flagSearch a key xs).steps+Z.steps+6*bw+6*a+18⟩).steps≤_
    cases Z.result <;> simp only [Bool.false_eq_true,if_false,if_true,h,List.length_cons,Nat.add_mul,one_mul]
    all_goals unfold flagSearchFee at ih ⊢; omega

def flagHeaderSpec {a b : ℕ} (width : ℕ) (mask : MaskFamily a b (Fin 64))
    (row : FlagRow (width+13*a)) (p : Page a b (Fin 64)) : Prop :=
  bitsValue row.key.val=pageCode width p ∧ row.flags=List.ofFn (maskWordAt mask p)

theorem flag_search_exact {a b : ℕ} (width : ℕ) (fit : b≤2^width)
    (mask : MaskFamily a b (Fin 64)) (p : Page a b (Fin 64))
    (rows : List (FlagRow (width+13*a))) (pages : List (Page a b (Fin 64)))
    (H : List.Forall₂ (flagHeaderSpec width mask) rows pages) (hit : p∈pages) :
    (flagSearch a (pageWord width p) rows).result=some (List.ofFn (maskWordAt mask p)) := by
  induction H with
  | nil => simp at hit
  | cons x h ih =>
    rename_i row page rs ps
    let key := pageWord width p
    let Z := A1R9.eqWord key.val row.key.val
    have hEq : Z.result=true ↔ p=page := by
      have E := (A1R9.eqWord_exact key.val row.key.val (key.property.trans row.key.property.symm)).1
      change Z.result=true↔_ at E
      rw [E,x.1]
      exact (page_code_injective width fit).eq_iff
    change (if Z.result then (⟨some row.flags,Z.steps+6*(width+13*a)+6*a+18⟩:Meter (Option (List Bool))) else
      ⟨(flagSearch a key rs).result,(flagSearch a key rs).steps+Z.steps+6*(width+13*a)+6*a+18⟩).result=_
    by_cases same : p=page
    · rw [if_pos (hEq.mpr same),same,x.2]
    · rw [if_neg (fun h=>same (hEq.mp h))]
      exact ih ((List.mem_cons.mp hit).resolve_left same)

def applyFlagTape {bw : ℕ} (a : ℕ) (key : Word bw) (source : List Bool)
    (rows : List (FlagRow bw)) : Meter (Option (List Bool)) :=
  let recv := flagSearch a key rows
  match recv.result with
  | none => ⟨none,recv.steps+4⟩
  | some bits =>
    let out := flipTape source bits
    ⟨some out.result,recv.steps+out.steps+4⟩

theorem actual_mask_slot_lookup {a b : ℕ} (width : ℕ) (fit : b≤2^width)
    (mask : MaskFamily a b (Fin 64)) (z : Physical a b (Fin 64))
    (rows : List (FlagRow (width+13*a))) (pages : List (Page a b (Fin 64)))
    (H : List.Forall₂ (flagHeaderSpec width mask) rows pages) (hit : z.1∈pages) :
    let machine := applyFlagTape a (pageWord width z.1) (List.ofFn (bits a z.2)) rows
    machine.result=some (List.ofFn (bits a (twistSeat mask z).2)) ∧
      machine.steps≤12+rows.length*flagSearchFee (width+13*a) a+8*a := by
  have E := flag_search_exact width fit mask z.1 rows pages H hit
  have fee := flag_search_cost a (pageWord width z.1) rows
  have F := actual_slot_flip_word mask z
  unfold applyFlagTape
  dsimp only at F ⊢
  rw [E]
  dsimp only
  rw [F.1,F.2]
  exact ⟨rfl,by omega⟩

#print axioms flag_search_cost
#print axioms flag_search_exact
#print axioms actual_mask_slot_lookup
end J6R24LegalLayout
