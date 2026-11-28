import J6R57ScopeFeeSidecar
import J6R54ExteriorOwnerWords
import J6R55TerminalOriginTape

/-! Native first-slot copies use finite gate arities, fixed addresses and a
real scan of the complete roster. These estimates concern the existing
R53/R54/R55 word routines, including the empty original gate. -/
namespace J6R58BootScope
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6OrientedHost J6R26DescriptorTree J6R21Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R49SourceLayout
open J6R51Peak J6R53OldOwner J6R54ExteriorOwner J6R55TerminalOrigin
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false

def originWidthFee (key prec pg : ℕ) := 3*key+3*prec+3*pg+22

theorem origin_fee_fits (key prec pg : ℕ) (present : Bool) :
    originFee key prec pg present≤originWidthFee key prec pg := by
  cases present <;> simp only [originFee,originWidthFee,Bool.false_eq_true,if_false,if_true] <;> omega

def rootGateWidthFee (gate key prec pg d : ℕ) :=
  originWidthFee key prec pg+(3*gate+5)*d+3*d+19

theorem original_encoded_gate_fee {w key prec pg d D : ℕ} (tag : Origin key prec pg)
    (port : Fin d→Word w) (G : Gate d) (fit : d≤D) :
    ownerDataFee (⟨tag,some (encodeGate port G)⟩ : OwnerData w key prec pg)≤
      rootGateWidthFee w key prec pg D := by
  have h := origin_fee_fits key prec pg tag.pageKey.isSome
  have lm := Nat.mul_le_mul_left (3*w+5) fit
  cases G <;> simp only [ownerDataFee,rootGateWidthFee,encodeGate,optGateFee,gateCopyFee,List.length_ofFn] <;> omega

theorem fresh_owner_width_fee {w key prec pg : ℕ} (stamp : Stamp key prec) (keyPage : Word pg) :
    ownerDataFee (freshOwnerData (gate:=w) stamp keyPage)=originWidthFee key prec pg+7 := by
  simp only [freshOwnerData,ownerDataFee,originFee,originWidthFee,Option.isSome_some,if_true,optGateFee]
  omega

theorem origin_tape_fee_by_actual_length {own w key prec pg : ℕ}
    (rows : RawRoster own w key prec pg) :
    (projectOriginTape rows).steps≤3+rows.length*(6*own+8+originWidthFee key prec pg) := by
  rw [project_origin_tape_exact]
  apply Nat.add_le_add_left
  exact uniform_sum_bound _ _ _ (fun row _=>by
    have pay := origin_fee_fits key prec pg row.payload.origin.pageKey.isSome
    omega)

theorem origin_tape_same_length {own w key prec pg : ℕ}
    (rows : RawRoster own w key prec pg) :
    (projectOriginTape rows).result.length=rows.length := by
  rw [project_origin_tape_exact]
  exact List.length_map _

theorem select_key_fee_by_actual_length {w : ℕ} (g : Word 6)
    (headers : List (OwnerGroup w)) :
    (selectOwnerKeys g headers).steps≤3+headers.length*(6*w+78) := by
  rw [select_owner_keys_exact]
  dsimp only
  have hc : ((headers.filter (fun x : OwnerGroup w=>decide (g=x.group))).map OwnerGroup.key).length≤headers.length := by
    rw [List.length_map]
    exact List.length_filter_le _ _
  refine (Nat.add_le_add_left (Nat.mul_le_mul_left (3*w+1) hc) (3+(3*w+77)*headers.length)).trans_eq ?_
  ring

#print axioms origin_fee_fits
#print axioms original_encoded_gate_fee
#print axioms fresh_owner_width_fee
#print axioms origin_tape_fee_by_actual_length
#print axioms origin_tape_same_length
#print axioms select_key_fee_by_actual_length
end J6R58BootScope
