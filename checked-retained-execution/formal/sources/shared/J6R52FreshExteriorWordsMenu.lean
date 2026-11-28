import J6R31RootResidentTablesJoin
import J6R51IngressPhysicalFile

/-! A width bound on the actual printed resident menu. It is a size
proof about typed packets, not a demand to precompute the raw roster
to choose its address width. Extra hot-cell information can only
reduce the upper bound. -/
namespace J6R52FreshExterior
open scoped Classical
open J6Mesh J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R15ModeCost J6R17ModeTape J6R24LegalLayout
open J6R28GeneratedRootFrame AOracleMachineTime
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12500000
set_option maxRecDepth 2500

theorem copies_fit_root_key (m : ℕ) : K m≤2^RootKey m := by
  rw [K,root_key_width_exact]
  exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)

theorem copy_width_above_one {m q : ℕ} (fit : K m<2^q) : 1<q := by
  by_contra small
  have hs : q≤1 := by omega
  have bound := Nat.pow_le_pow_right (show 0<(2:ℕ) by decide) hs
  have h := (mesh_seats m).2.1
  change 2^q≤2 at bound
  omega

theorem hot_count_le_printed (m : ℕ) (i : Fin (a m)) :
    Fintype.card (HotCell i)≤D m := by
  have H := Fintype.card_le_of_injective
    (fun c : HotCell i=>c.val) Subtype.val_injective
  exact H.trans_eq (literal_cell_card m)

theorem packet_mode_count_printed (m p : ℕ) (i : Fin (a m)) :
    Fintype.card (PacketMode i (K m) (2^(i.val+1)) p)≤M m*(p-1) := by
  have ht : 2^(i.val+1)≤L m := by
    unfold L
    exact Nat.pow_le_pow_right (by decide) i.isLt
  calc
    Fintype.card (PacketMode i (K m) (2^(i.val+1)) p)
        = Fintype.card (HotCell i)*(K m*(2^(i.val+1)*(p-1))) := by
          rw [Fintype.card_congr (orderedMode i (K m) (2^(i.val+1)) p)]
          simp only [Fintype.card_prod,Fintype.card_fin]
    _ ≤ D m*(K m*(L m*(p-1))) :=
      Nat.mul_le_mul (hot_count_le_printed m i)
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ht))
    _ = M m*(p-1) := by rw [←mesh_product]; ring

theorem root_modes_length_is_card {q r c d : ℕ} (m p : ℕ)
    (hq : 0<q) (i : Fin (a m)) (hi : i.val+1<q)
    (cpy pr : Word q) (hc : cpy.val=K m) (hp : pr.val=p) (positive : 0<p)
    (raw : List (SignedHalfPort r c d)) :
    (writeResidents m hq i cpy pr raw).result.roster.modes.length=
      Fintype.card (PacketMode i (K m) (2^(i.val+1)) p) := by
  obtain ⟨entries,nd,all,sp,_,_,_,_⟩ := root_ordered_roster_exact hq i hi cpy pr hc hp positive
  change (rootRoster hq m i.val cpy pr).result.modes.length=_
  rw [sp,List.length_map]
  exact J6R51Ingress.full_roster_length entries nd all

def rootCodeWidth (m base : ℕ) : ℕ :=
  Nat.clog 2 (M m*(J6SourcePrecision.printed m base-1)+2)

theorem root_code_positive (m base : ℕ) : 0<rootCodeWidth m base := by
  unfold rootCodeWidth
  exact Nat.clog_pos (by decide) (by omega)

theorem printed_root_code_fit {q r c d : ℕ} (m base : ℕ)
    (hq : 0<q) (hQ : 1<q) (cpy pr : Word q)
    (hc : cpy.val=K m) (hp : pr.val=J6SourcePrecision.printed m base)
    (raw : List (SignedHalfPort r c d)) :
    1+(writeResidents m hq (oddAxis m) cpy pr raw).result.roster.modes.length<2^rootCodeWidth m base := by
  rw [root_modes_length_is_card m (J6SourcePrecision.printed m base) hq (oddAxis m) hQ cpy pr hc hp
    (printed_precision_positive m base) raw]
  have H := packet_mode_count_printed m (J6SourcePrecision.printed m base) (oddAxis m)
  have cap := Nat.le_pow_clog (show 1<(2:ℕ) by decide)
    (M m*(J6SourcePrecision.printed m base-1)+2)
  change M m*(J6SourcePrecision.printed m base-1)+2≤2^rootCodeWidth m base at cap
  omega

/-- A simpler physical implementation can use this conservative width
when its original precision word already fits in q bits. -/
def expandedCodeWidth (m q : ℕ) : ℕ := lambda m+q+1

theorem expanded_code_fit {q r c d : ℕ} (m base : ℕ)
    (hq : 0<q) (hQ : 1<q) (cpy pr : Word q)
    (hc : cpy.val=K m) (hp : pr.val=J6SourcePrecision.printed m base)
    (raw : List (SignedHalfPort r c d)) :
    1+(writeResidents m hq (oddAxis m) cpy pr raw).result.roster.modes.length<2^expandedCodeWidth m q := by
  let p := J6SourcePrecision.printed m base
  rw [root_modes_length_is_card m p hq (oddAxis m) hQ cpy pr hc hp
    (printed_precision_positive m base) raw]
  have h := packet_mode_count_printed m p (oddAxis m)
  have f : p<2^q := by
    change J6SourcePrecision.printed m base<2^q
    rw [←hp]
    exact val_lt pr
  have B : M m*(p-1)≤2^(lambda m+q) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have e : 2^expandedCodeWidth m q=2^(lambda m+q)*2 := by rw [expandedCodeWidth,pow_succ]
  have pos : 1<2^(lambda m+q) := one_lt_pow₀ (by decide) (by omega)
  rw [e]
  omega

#print axioms copies_fit_root_key
#print axioms copy_width_above_one
#print axioms hot_count_le_printed
#print axioms packet_mode_count_printed
#print axioms root_modes_length_is_card
#print axioms root_code_positive
#print axioms printed_root_code_fit
#print axioms expanded_code_fit
end J6R52FreshExterior
