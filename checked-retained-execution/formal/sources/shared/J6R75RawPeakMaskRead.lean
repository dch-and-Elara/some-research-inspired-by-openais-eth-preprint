import J6R75RawPeakStockScanner
import J6R58ActivePrepMaskTable

/-! The installed literal probe table and the actual sequential
lookup. Its returned byte list is a real copy of the addressed row.
A conservative reserve permits preceding copies to remain during
the lookup, rather than assuming whole-list reclamation. -/
namespace J6R75RawPeak
open AOracleMachineTime J6R58ActivePrep

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3500
set_option maxHeartbeats 6300000
set_option Elab.async false

def resumeMaskScan (seen : Meter (List Bool)) (finish : Meter (Option (List Bool))) :
    Meter (Option (List Bool)) :=
  ⟨finish.result,seen.steps+finish.steps+4⟩

theorem actual_mask_scan_has_its_original_prefix_continuations
    (pre : List (List Bool)) (row : List Bool) (post : List (List Bool)) :
    scanMask pre.length (pre++row::post)=
      (pre.map copyBits).foldr resumeMaskScan
        ⟨some (copyBits row).result,(copyBits row).steps+4⟩ := by
  induction pre with
  | nil=>rfl
  | cons q qs ih=>
    change resumeMaskScan (copyBits q) (scanMask qs.length (qs++row::post))=
      resumeMaskScan (copyBits q) _
    exact congrArg (resumeMaskScan (copyBits q)) ih

theorem mounted_mask_addressed_copy_keeps_the_same_named_table_bytes
    {e n m : ℕ} {fit : n≤2^e} (T : MaskTable e n fit)
    (allowed : m≤n) (i : Fin m) (pre : List (List Bool)) (row : List Bool) (post : List (List Bool))
    (split : T.raw=pre++row::post) (address : pre.length=i.val)
    (resident roof : ℕ) (live : resident≤roof) :
    let copy := (copyBits row)
    let previous := pre.map (fun x=>(copyBits x).result)
    let seen := (pre.map copyBits).foldr resumeMaskScan ⟨some copy.result,copy.steps+4⟩
    scanMask i.val T.raw=seen ∧
    T.readRaw allowed i=⟨copy.result,seen.steps⟩ ∧
    resident+(gridMemoryBits T.raw+gridMemoryBits previous+copy.result.length)≤
      roof+(e*n+e*(i.val+1)) := by
  have ran : scanMask i.val T.raw=
      (pre.map copyBits).foldr resumeMaskScan ⟨some (copyBits row).result,(copyBits row).steps+4⟩ := by
    rw [split,←address]
    exact actual_mask_scan_has_its_original_prefix_continuations pre row post
  have out :
      ((pre.map copyBits).foldr resumeMaskScan ⟨some (copyBits row).result,(copyBits row).steps+4⟩).result=
        some (copyBits row).result := by
    clear ran split address
    induction pre with
    | nil=>rfl
    | cons x xs ih=>exact ih
  have cop : (pre.map fun x=>(copyBits x).result)=pre := by
    have all : ∀ r∈pre,(copyBits r).result=r := fun r _=>congrArg Meter.result (copy_bits_exact r)
    apply List.map_congr_left at all
    exact all.trans (List.map_id _)
  have widths (r : List Bool) (inPre : r∈pre) : r.length=e := T.width r
    (split.symm ▸ List.mem_append_left _ inPre)
  have oneWidth : row.length=e := T.width row (split.symm ▸ List.mem_append_right _ List.mem_cons_self)
  refine ⟨ran,?_,Nat.add_le_add live ?_⟩
  · unfold MaskTable.readRaw
    rw [ran]
    dsimp only
    rw [out]
    rfl
  · rw [uniform_grid_bits e T.raw T.width,T.length,cop,uniform_grid_bits e pre widths,
      copy_bits_exact,oneWidth,address,Nat.mul_succ]
    omega

theorem literal_preloaded_mask_install_can_keep_both_real_tables
    {e n : ℕ} {fit : n≤2^e} (T : MaskTable e n fit)
    (resident roof : ℕ) (live : resident≤roof) :
    T.install.result.raw=T.raw ∧
    resident+(gridMemoryBits T.raw+gridMemoryBits T.install.result.raw)≤roof+2*(e*n) := by
  have eq : T.install.result.raw=T.raw := congrArg (fun r=>(Meter.result r).raw) T.installed_exact
  have bytes : gridMemoryBits T.raw=e*n := by rw [uniform_grid_bits e T.raw T.width,T.length]
  refine ⟨eq,Nat.add_le_add live ?_⟩
  rw [eq,bytes]
  omega

#print axioms actual_mask_scan_has_its_original_prefix_continuations
#print axioms mounted_mask_addressed_copy_keeps_the_same_named_table_bytes
#print axioms literal_preloaded_mask_install_can_keep_both_real_tables
end J6R75RawPeak
