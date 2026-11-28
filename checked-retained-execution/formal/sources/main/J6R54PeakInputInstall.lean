import J6R53PeakAddonCore

/-! The real installAddons recursion retains one paid address/payload
copy for the current matched raw row. This factorization follows its
exact continuation, including the Option failure branch of a tail. -/
namespace J6R54PeakInput
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6R36ChildFramedRoute J6R41StructuredAllPaths J6R51Peak J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 14500000

variable {w owner a key prec page : ℕ} {K : Type*}
local notation "Raw" => Addon owner a key prec page
local notation "Row" => RefRow w Raw

def paidIndexHead (p : PortRow w) (x : Raw) : Meter Row :=
  let addr := duplicateWord p.address
  let value := copyAddon x
  ⟨⟨addr.result,value.result⟩,addr.steps+value.steps⟩

def resumePaidIndexHeads (heads : List (Meter Row)) (tail : Meter (Option (List Row))) :
    Meter (Option (List Row)) :=
  heads.foldr (fun h t=>⟨t.result.map (h.result::·),h.steps+t.steps+7⟩) tail

theorem actual_index_installer_resumes_after_paid_heads
    (recPort : K→PortRow w) (raw : K→Raw) (before : List K) (ports : List (PortRow w)) (values : List Raw) :
    installAddons (before.map recPort++ports) (before.map raw++values)=
      resumePaidIndexHeads (before.map (fun x=>paidIndexHead (recPort x) (raw x))) (installAddons ports values) := by
  induction before with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.cons_append,installAddons,resumePaidIndexHeads,List.foldr_cons,paidIndexHead] at *
    rw [ih]

theorem selected_index_heads_are_the_actual_installed_rows
    (recPort : K→PortRow w) (raw : K→Raw) (before after : List K) :
    (((installAddons ((before++after).map recPort) ((before++after).map raw)).result.getD []).take before.length)=
       before.map (fun x=>(paidIndexHead (recPort x) (raw x)).result) := by
  rw [(installed_addons_exact (before++after) recPort raw).1]
  simp only [Option.getD_some,List.map_append]
  induction before with
  | nil => rfl
  | cons x xs ih =>
    simp [paidIndexHead,duplicate_word_exact,copy_addon_exact,ih]

theorem selected_install_prefix_fits_actual_column_width
    (recPort : K→PortRow w) (raw : K→Raw) (before after : List K) :
    ((((installAddons ((before++after).map recPort) ((before++after).map raw)).result.getD []).take before.length).flatMap indexedAddonBits).length≤before.length*(w+addonCap owner a key prec page) := by
  rw [selected_index_heads_are_the_actual_installed_rows]
  have h := indexed_rows_uniform_cap (before.map (fun x=>(paidIndexHead (recPort x) (raw x)).result))
  rw [List.length_map] at h
  exact h

#print axioms actual_index_installer_resumes_after_paid_heads
#print axioms selected_index_heads_are_the_actual_installed_rows
#print axioms selected_install_prefix_fits_actual_column_width
end J6R54PeakInput
