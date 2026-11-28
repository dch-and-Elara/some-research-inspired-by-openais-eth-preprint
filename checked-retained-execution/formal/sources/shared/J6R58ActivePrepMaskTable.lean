import NativeProbeRing
import A1R10Word

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option Elab.async false

/-! A raw ordered public mask table is distinct from a family of metered
mask oracles.  Installation copies its actual bits once.  Lookup
moves a sequential row cursor to the requested slot, reads actual bits,
and never recomputes or calls a supplied mask operation. -/
namespace J6R58ActivePrep
open AOracleMachineTime

def copyBits : List Bool → Meter (List Bool)
  | [] => ⟨[],1⟩
  | x::xs => let t := copyBits xs; ⟨x::t.result,t.steps+3⟩

theorem copy_bits_exact (bs : List Bool) :
    copyBits bs=⟨bs,3*bs.length+1⟩ := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [copyBits,ih,List.length_cons]
    exact congrArg (Meter.mk (b::bs)) (by omega)

def copyTable : List (List Bool) → Meter (List (List Bool))
  | [] => ⟨[],2⟩
  | row::tail =>
    let x := copyBits row
    let xs := copyTable tail
    ⟨x.result::xs.result,x.steps+xs.steps+4⟩

theorem copy_table_exact (rows : List (List Bool)) (e : ℕ)
    (well : ∀ row ∈ rows,row.length=e) :
    copyTable rows=⟨rows,2+rows.length*(3*e+5)⟩ := by
  induction rows with
  | nil => simp only [copyTable,List.length_nil,Nat.zero_mul,Nat.add_zero]
  | cons row tail ih =>
    have hr := well row (List.mem_cons_self)
    have ht := ih (fun a ha=>well a (List.mem_cons_of_mem _ ha))
    rw [copyTable,copy_bits_exact,hr,ht]
    have h : 3*e+1+(2+tail.length*(3*e+5))+4=2+(row::tail).length*(3*e+5) := by
      simp only [List.length_cons,Nat.succ_mul]
      omega
    change Meter.mk (row::tail) (3*e+1+(2+tail.length*(3*e+5))+4)=_
    rw [h]

def scanMask : ℕ → List (List Bool) → Meter (Option (List Bool))
  | _,[] => ⟨none,2⟩
  | 0,row::_ =>
    let x := copyBits row
    ⟨some x.result,x.steps+4⟩
  | j+1,row::tail =>
    let x := copyBits row
    let y := scanMask j tail
    ⟨y.result,x.steps+y.steps+4⟩

theorem scan_mask_exact (raw : List (List Bool)) (e : ℕ)
    (well : ∀ row ∈ raw,row.length=e) (j : ℕ) (hit : j<raw.length) :
    scanMask j raw=⟨some (raw[j]'hit),(j+1)*(3*e+5)⟩ := by
  induction raw generalizing j with
  | nil => simp at hit
  | cons row tail ih =>
    have hr := well row (List.mem_cons_self)
    cases j with
    | zero =>
      simp only [scanMask,copy_bits_exact,hr,List.getElem_cons_zero,Nat.zero_add,Nat.one_mul]
    | succ j =>
      have lt : j<tail.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hit
      have t := ih (fun a ha=>well a (List.mem_cons_of_mem _ ha)) j lt
      rw [scanMask,copy_bits_exact,hr,t]
      have h : 3*e+1+(j+1)*(3*e+5)+4=(j.succ+1)*(3*e+5) := by
        rw [Nat.succ_eq_add_one]
        ring
      change Meter.mk (some (tail[j]'lt)) (3*e+1+(j+1)*(3*e+5)+4)=_
      rw [h]
      rfl

/-- The proof identifies concrete raw bytes with the installed native
certificate in its original ordering, not an arbitrary bit roster. -/
structure MaskTable (e n : ℕ) (fit : n≤2^e) where
  raw : List (List Bool)
  certified : raw=List.ofFn (fun j => List.ofFn (NativeProbeRing.chosenRep e n fit j))

namespace MaskTable

theorem length {e n : ℕ} {fit : n≤2^e} (T : MaskTable e n fit) : T.raw.length=n := by
  rw [T.certified,List.length_ofFn]

theorem width {e n : ℕ} {fit : n≤2^e} (T : MaskTable e n fit) (row : List Bool)
    (hit : row∈T.raw) : row.length=e := by
  rw [T.certified,List.mem_ofFn] at hit
  obtain ⟨j,H⟩ := hit
  rw [← H,List.length_ofFn]

/-- The chosen table at a shorter live call is a literal prefix, since
the printed model reuses the same field enumeration at every call. -/
theorem representative_prefix {e n m : ℕ} {fit : n≤2^e} {small : m≤2^e}
    (nested : m≤n) (j : Fin m) :
    NativeProbeRing.chosenRep e n fit (Fin.castLE nested j)=
      NativeProbeRing.chosenRep e m small j := by
  unfold NativeProbeRing.chosenRep
  congr 1

def install {e n : ℕ} {fit : n≤2^e} (T : MaskTable e n fit) :
    Meter (MaskTable e n fit) :=
  let q := copyTable T.raw
  ⟨⟨q.result,(congrArg Meter.result (copy_table_exact T.raw e T.width)).trans T.certified⟩,q.steps⟩

theorem installed_exact {e n : ℕ} {fit : n≤2^e} (T : MaskTable e n fit) :
    T.install=⟨T,2+n*(3*e+5)⟩ := by
  cases T with
  | mk raw certified =>
    have eq := copy_table_exact raw e (MaskTable.width ⟨raw,certified⟩)
    have len := MaskTable.length ⟨raw,certified⟩
    simp only [install,eq,len]

def readRaw {e n m : ℕ} {fit : n≤2^e} (T : MaskTable e n fit)
    (_ : m≤n) (j : Fin m) : Meter (List Bool) :=
  let z := scanMask j.val T.raw
  ⟨z.result.getD [],z.steps⟩

theorem read_raw_exact {e n m : ℕ} {fit : n≤2^e} {small : m≤2^e} (T : MaskTable e n fit)
    (nested : m≤n) (j : Fin m) :
    T.readRaw nested j=
       ⟨List.ofFn (NativeProbeRing.chosenRep e m small j),(j.val+1)*(3*e+5)⟩ := by
  have hit : j.val<T.raw.length := T.length.symm ▸ j.isLt.trans_le nested
  have one : T.raw[j.val]'hit=List.ofFn (NativeProbeRing.chosenRep e m small j) := by
    let k := Fin.castLE nested j
    let ref := List.ofFn (fun a : Fin n=>List.ofFn (NativeProbeRing.chosenRep e n fit a))
    have href : k.val<ref.length := by simpa only [ref,List.length_ofFn] using k.isLt
    have hh : T.raw[k.val]?=ref[k.val]? :=
      congrArg (fun r : List (List Bool) => r[k.val]?) T.certified
    rw [getElem?_pos T.raw k.val hit,getElem?_pos ref k.val href,Option.some.injEq] at hh
    have eqref : ref[k.val]=List.ofFn (NativeProbeRing.chosenRep e n fit k) := by
      simp only [ref,List.getElem_ofFn]
    rw [eqref] at hh
    exact hh.trans (congrArg List.ofFn (representative_prefix nested j))
  unfold readRaw
  rw [scan_mask_exact T.raw e T.width j.val hit,one]
  rfl

end MaskTable

#print axioms scan_mask_exact
#print axioms copy_table_exact
#print axioms MaskTable.representative_prefix
#print axioms MaskTable.installed_exact
#print axioms MaskTable.read_raw_exact
end J6R58ActivePrep

