import J6R53OldOwnerRootEmit
import J6R53TerminalGateGeometry
import J6R30GeneratedRootLayoutReceipt

/-! Read suffix words from the actually emitted stable-root port
records. The output uses page/slot (not a source-rank surrogate or a
signed half-address), and every stable wire appears in the bank. -/
namespace J6R53OldOwnerRoot
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost
open J6R25PreparedSupply J6R31RootResidentTables J6R30GeneratedRootLayout
open J6R32RootGeneratedRegistryInputs J6R53TerminalGate J6R24LegalLayout J6OrientedHost J6Mesh
open J6R26StablePreparedRoot J6R20Ancestor J6R21Ancestor J6R10Repack
open J6R28GeneratedRootFrame J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3300
set_option maxHeartbeats 16000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

abbrev SuffixKeyWidth (m : ℕ) := 12*a m+printedRankWidth m
abbrev SuffixWordWidth (m : ℕ) := pageKeyWidth m+a m
abbrev SuffixBank (m : ℕ) := List (RefRow (SuffixKeyWidth m) (Word (SuffixWordWidth m)))

def appendSeatSuffix (m : ℕ) (s : SeatField (a m) (pageKeyWidth m)) :
    Meter (Word (SuffixWordWidth m)) :=
  let slot := copyFixed s.slot
  let out := appendBits s.page.bits slot.result.bits
  ⟨⟨out.result,by
      change (appendBits s.page.bits (copyFixed s.slot).result.bits).result.length=_
      rw [append_bits_exact,List.length_append,s.page.size,(copyFixed s.slot).result.size]⟩,
    slot.steps+out.steps+4⟩

theorem append_seat_suffix_exact (m : ℕ) (s : SeatField (a m) (pageKeyWidth m)) :
    (appendSeatSuffix m s).result.bits=s.page.bits++s.slot.bits ∧
      (appendSeatSuffix m s).steps=(3*a m+1)+(2+4*pageKeyWidth m)+4 := by
  unfold appendSeatSuffix
  simp only [copy_fixed_exact,append_bits_exact,s.page.size,and_self]

def readMountedSuffix (m : ℕ) (axis : List Bool) {r c d : ℕ} (x : MountedPort r c d) :
    Meter (RefRow (SuffixKeyWidth m) (Word (SuffixWordWidth m))) :=
  let id := fitWord (SuffixKeyWidth m) x.base.key
  let seat := buildSeatField (a m) (RootKey m) axis x.base.anchor.anchor
  let suffix := appendSeatSuffix m seat.result
  ⟨⟨id.result,suffix.result⟩,id.steps+seat.steps+suffix.steps+7⟩

theorem mounted_suffix_is_original {V : Type} [Fintype V] {m n r c d : ℕ}
    {P : Plant V m n} (C : LiteralPortFile P r c d) (axis : List Bool)
    (clock : axis.length=(oddAxis m).val) (x : RootWire m) :
    (readMountedSuffix m axis (trueMounted C x)).result=
      ⟨stableWireKeyWord m x,rootWireSuffix P x⟩ := by
  let k := SuffixKeyWidth m
  let seat := buildSeatField (a m) (RootKey m) axis (sourceAnchor m x).anchor
  have given := (source_seat_field C (oddAxis m) axis clock x).1
  have name : (fitWord k (expectedBase m x).key).result=stableWireKeyWord m x := by
    apply word_bits_inj
    exact fit_word_value k _ (base_key_width m x)
  have suffix : (appendSeatSuffix m seat.result).result=rootWireSuffix P x := by
    apply word_bits_inj
    rw [(append_seat_suffix_exact m seat.result).1]
    change seat.result.page.bits++seat.result.slot.bits=_
    rw [show seat.result=physicalSeatField (rootChart P) (oddAxis m) (residentPageKey m) x from given]
    rfl
  change RefRow.mk (fitWord k (expectedBase m x).key).result
    (appendSeatSuffix m seat.result).result=_
  rw [name,suffix]

def collectRootSuffixes (m : ℕ) (axis : List Bool) {r c d : ℕ} :
    List (MountedPort r c d)→Meter (SuffixBank m)
  | []=>⟨[],3⟩
  | x::xs=>
    let h := readMountedSuffix m axis x
    let tail := collectRootSuffixes m axis xs
    ⟨h.result::tail.result,h.steps+tail.steps+4⟩

theorem collect_root_suffix_rows (m : ℕ) (axis : List Bool) {r c d : ℕ} (xs : List (MountedPort r c d)) :
    collectRootSuffixes m axis xs=⟨xs.map (fun x=>(readMountedSuffix m axis x).result),
      3+(xs.map (fun x=>(readMountedSuffix m axis x).steps+4)).sum⟩ := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [collectRootSuffixes,ih,List.map_cons,List.sum_cons]
    congr 1
    omega

def paidRootSuffixBank (m : ℕ) (axis : List Bool) {r c d : ℕ} (literal : List (SignedHalfPort r c d)) :
    Meter (SuffixBank m) :=
  let b := generatedPaddedPorts m literal
  let out := collectRootSuffixes m axis b.result
  ⟨out.result,b.steps+out.steps+5⟩

theorem paid_root_suffix_bank_actual {V : Type} [Fintype V] {m n r c d : ℕ}
    {P : Plant V m n} (C : LiteralPortFile P r c d) (axis : List Bool) (clock : axis.length=(oddAxis m).val) :
    let out := paidRootSuffixBank m axis C.raw
    out.result=(actualWires m).map (fun x=>⟨stableWireKeyWord m x,rootWireSuffix P x⟩) ∧
      out.steps=(generatedPaddedPorts m C.raw).steps+
        (3+((generatedPaddedPorts m C.raw).result.map (fun x=>(readMountedSuffix m axis x).steps+4)).sum)+5 := by
  unfold paidRootSuffixBank
  dsimp only
  rw [collect_root_suffix_rows]
  refine ⟨?_,rfl⟩
  dsimp only
  rw [(generated_padded_ports_exact C).1,List.map_map]
  apply List.map_congr_left
  intro x _
  exact mounted_suffix_is_original C axis clock x

theorem actual_suffix_bank_covers_original_wire {V : Type} [Fintype V] {m n r c d : ℕ}
    {P : Plant V m n} (C : LiteralPortFile P r c d) (axis : List Bool)
    (clock : axis.length=(oddAxis m).val) (x : RootWire m) :
    (locate (stableWireKeyWord m x) (paidRootSuffixBank m axis C.raw).result).result=
      some (rootWireSuffix P x) := by
  rw [(paid_root_suffix_bank_actual C axis clock).1]
  apply locate_hit
  · exact List.mem_map.mpr ⟨x,(ordered_wires_exact (constantRootWord m)
      (printed_room m) (printed_half_correct m)).2 x,rfl⟩
  · intro r hr hkey
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hr
    have e : y=x := stable_wire_key_injective m hkey
    subst y
    rfl

#print axioms append_seat_suffix_exact
#print axioms mounted_suffix_is_original
#print axioms collect_root_suffix_rows
#print axioms paid_root_suffix_bank_actual
#print axioms actual_suffix_bank_covers_original_wire
end
end J6R53OldOwnerRoot
