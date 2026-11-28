import J6R58LeafScalePrecision
import J6R24MeteredRecursionTight
import J6R12RepackSchedule

/-! The exterior root arrives at its creation precision, not at the
base precision. Both are kept in the original absolute schedule. -/
namespace J6R66LeafTariff
open J6Mesh J6R24MeteredRecursion J6R58LeafScale

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 15000000

theorem same_printed_source_mesh (m native : ℕ) (hn : native≤m) :
    J1PPrinted.stepA (Nat.clog 2 (physicalSize m native)) 0=a m :=
  J6R12Repack.mesh_root_bits m native hn

theorem actual_mesh_M_at_most_twice_source (m native : ℕ) (hn : native≤m) :
    M m≤2*physicalSize m native := by
  have h := physicalSize_ceiling m native hn
  have bpos : 0<(2:ℕ)^(lambda m-1) := by positivity
  have s1 : 1<physicalSize m native := (show 1≤_ by omega).trans_lt h.1
  change 2^lambda m≤2*physicalSize m native
  rw [←h.2.2]
  exact printed_clog_power_le_twice_size _ s1

theorem printed_exterior_register_size (m native base C : ℕ)
    (hn : native≤m) (pos : 0<C) (baseFit : base≤C*physicalSize m native) :
    J6SourcePrecision.printed m base≤161*C*(physicalSize m native)^2 := by
  let s := physicalSize m native
  have aLam : a m≤lambda m := by unfold a lambda; omega
  have uLam : u m≤lambda m := by unfold u lambda; omega
  have uPos : 0<u m := by unfold u; have h := b_pos m; omega
  have aM : a m+1≤M m := (Nat.succ_le_succ aLam).trans
    (J9PrintedSchedule.next_le_two_power (lambda m))
  have uM : u m≤M m := uLam.trans
    ((Nat.le_succ _).trans (J9PrintedSchedule.next_le_two_power (lambda m)))
  have height : J6SourcePrecision.h m≤4*M m := simple_height_cap uPos uM
  have mesh : L m≤M m := Nat.pow_le_pow_right (by decide) aLam
  have hM : M m≤2*s := actual_mesh_M_at_most_twice_source m native hn
  have hs : 0<s := (Nat.zero_le _).trans_lt (physicalSize_ceiling m native hn).1
  have baseSquare : base≤C*s^2 := baseFit.trans (Nat.mul_le_mul_left _
    (by rw [pow_two]; exact Nat.le_mul_of_pos_right _ hs))
  have widen : 160*s^2≤160*C*s^2 := Nat.mul_le_mul_right _
    (Nat.le_mul_of_pos_right _ pos)
  calc
    _≤base+8*(4*M m)*M m+8*M m*M m := by
      unfold J6SourcePrecision.printed
      gcongr
    _=base+40*(M m)^2 := by ring
    _≤base+40*(2*s)^2 := by gcongr
    _=base+160*s^2 := by ring
    _≤ C*s^2+160*C*s^2 := Nat.add_le_add baseSquare widen
    _=_ := by ring

theorem native_mode_count_at_absolute_receiver
    {s C p modes : ℕ} (large : 1024≤Nat.clog 2 s) (small : C≤s)
    (width : p≤321*C*s^2) (area : modes≤3*(C*s)*p) :
    modes+2≤2^(6*Nat.clog 2 s) := by
  let lamS := Nat.clog 2 s
  have hs : 0<s := (by decide : 0<(1:ℕ)).trans <|
    (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).mp
      (show 0<lamS from (by decide : 0<(1024:ℕ)).trans_le large)
  have bound : modes+2≤963*s^5+2 := by
    calc
      _≤3*(C*s)*(321*C*s^2)+2 :=
        Nat.add_le_add_right (area.trans (Nat.mul_le_mul_left _ width)) _
      _≤3*(s*s)*(321*s*s^2)+2 := by gcongr
      _=_ := by ring
  calc
    _≤963*s^5+2 := bound
    _≤965*s^5 := by
      rw [show (965:ℕ)=963+2 by decide,Nat.add_mul]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.pow_pos hs)) _
    _≤2^10*(2^lamS)^5 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)
    _=2^(10+lamS*5) := by rw [←pow_mul,←pow_add]
    _≤_ := Nat.pow_le_pow_right (by decide) (by change 10+lamS*5≤6*lamS; omega)

#print axioms same_printed_source_mesh
#print axioms actual_mesh_M_at_most_twice_source
#print axioms printed_exterior_register_size
#print axioms native_mode_count_at_absolute_receiver
end J6R66LeafTariff
