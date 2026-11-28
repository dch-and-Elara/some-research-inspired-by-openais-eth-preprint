import J6R54PublicFamilyWords
import J6R17ModeTapeCodec
import Mathlib.Data.Nat.Log

/-! A real sequential pass over the existing raw mode tape. The extra
counter holds the binary value N+1, not N copied rows and not a word of
arbitrary advertised mode-code width. Each row is passed once, including
its five bit fields; carry work has an exact amortized potential law. -/
namespace J6R102NativeCodeMeter
open AOracleMachineTime J6R15ModeCost J6R54PublicFamily J6R17ModeTape
open J6R14LayoutCost

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 4500000

def bump : List Bool → Meter (List Bool)
  | [] => ⟨[true],5⟩
  | false::bs => ⟨true::bs,5⟩
  | true::bs =>
    let rest := bump bs
    ⟨false::rest.result,5+rest.steps⟩

def ones : List Bool → ℕ
  | [] => 0
  | bit::bs => bit.toNat+ones bs

theorem bump_value (bs : List Bool) : bitsValue (bump bs).result=bitsValue bs+1 := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b
    · simp only [bump,bitsValue,Bool.toNat_true,Bool.toNat_false]
      omega
    · simp only [bump,bitsValue,Bool.toNat_true,Bool.toNat_false,ih]
      omega

theorem bump_potential (bs : List Bool) :
    (bump bs).steps+5*ones (bump bs).result=10+5*ones bs := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b
    · simp only [bump,ones,Bool.toNat_true,Bool.toNat_false]
      omega
    · simp only [bump,ones,Bool.toNat_true,Bool.toNat_false]
      omega

inductive Canonical : List Bool → Prop
  | empty : Canonical []
  | one : Canonical [true]
  | more (b : Bool) {t : Bool} {ts : List Bool} :
      Canonical (t::ts) → Canonical (b::t::ts)

theorem canonical_prepend {bs : List Bool} (hb : Canonical bs) (hne : bs≠[]) (b : Bool) :
    Canonical (b::bs) := by
  cases bs with
  | nil => exact (hne rfl).elim
  | cons t ts => exact .more b hb

theorem bump_canonical {bs : List Bool} (h : Canonical bs) :
    Canonical (bump bs).result := by
  induction h with
  | empty => exact .one
  | one => exact .more false .one
  | @more b t ts canon ih =>
    cases b
    · exact .more true canon
    · apply canonical_prepend ih _ false
      intro he
      have hv := bump_value (t::ts)
      rw [he,bitsValue] at hv
      omega

theorem canonical_lower {bs : List Bool} (h : Canonical bs) (hne : bs≠[]) :
    2^(bs.length-1)≤bitsValue bs := by
  induction h with
  | empty => exact (hne rfl).elim
  | one => decide
  | @more b t ts ht ih =>
    have lower := ih (by simp)
    simp only [List.length_cons,Nat.succ_sub_one] at lower ⊢
    rw [pow_succ,bitsValue]
    omega

/-- A sequential read-and-advance operation, with a terminating delimiter. -/
def passBits : List Bool → Meter Unit
  | [] => ⟨(),1⟩
  | _::bs =>
    let rest := passBits bs
    ⟨rest.result,rest.steps+2⟩

theorem pass_bits_fee (bs : List Bool) : (passBits bs).steps=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [passBits,List.length_cons,ih]
    omega

def passMode {q : ℕ} (x : RawMode q) : Meter Unit :=
  (passBits x.key.1).bind fun _ =>
    (passBits x.key.2).bind fun _ =>
      (passBits x.page.bits).bind fun _ =>
        (passBits x.tile.bits).bind fun _ => passBits x.weight.bits

theorem pass_mode_fee {q : ℕ} (x : RawMode q) :
    (passMode x).steps=2*(x.key.1.length+x.key.2.length+3*q)+5 := by
  simp only [passMode,Meter.bind,pass_bits_fee,x.page.size,x.tile.size,x.weight.size]
  omega

def countModesFrom {q : ℕ} : List (RawMode q) → List Bool → Meter (List Bool)
  | [], b => ⟨b,3⟩
  | x::xs, b =>
    let inrow := passMode x
    let inc := bump b
    let rest := countModesFrom xs inc.result
    ⟨rest.result,inrow.steps+inc.steps+rest.steps+6⟩

theorem count_modes_from_exact {q : ℕ} (xs : List (RawMode q)) (b : List Bool)
    (hc : Canonical b) :
    let out := countModesFrom xs b
    bitsValue out.result=bitsValue b+xs.length ∧ Canonical out.result ∧
      out.steps+5*ones out.result =
        3+(xs.map (fun x=>(passMode x).steps)).sum+16*xs.length+5*ones b := by
  induction xs generalizing b with
  | nil =>
    simp only [countModesFrom,List.map_nil,List.sum_nil,List.length_nil,
      Nat.mul_zero,Nat.add_zero]
    exact ⟨trivial,hc,trivial⟩
  | cons x xs ih =>
    obtain ⟨hv,hc',hf⟩ := ih (bump b).result (bump_canonical hc)
    have vb := bump_value b
    have fb := bump_potential b
    simp only [countModesFrom,List.length_cons,List.map_cons,List.sum_cons]
    exact ⟨by rw [hv,vb]; omega,hc',by omega⟩

/-- Start at one, so its significant-bit count is ceil-log of N+2,
including when the actual source has no modes. -/
def countModes {q : ℕ} (xs : List (RawMode q)) : Meter (List Bool) :=
  let scan := countModesFrom xs [true]
  ⟨scan.result,scan.steps+3⟩

theorem count_modes_exact {q : ℕ} (xs : List (RawMode q)) :
    let out := countModes xs
    bitsValue out.result=1+xs.length ∧ Canonical out.result ∧
      out.steps+5*ones out.result =
        11+(xs.map (fun x=>(passMode x).steps)).sum+16*xs.length := by
  obtain ⟨hv,hc,hf⟩ := count_modes_from_exact xs [true] .one
  exact ⟨hv,hc,by
    change (countModesFrom xs [true]).steps+3+5*ones (countModesFrom xs [true]).result=_
    change (countModesFrom xs [true]).steps+5*ones (countModesFrom xs [true]).result=
      3+(xs.map (fun x=>(passMode x).steps)).sum+16*xs.length+5 at hf
    omega⟩

theorem counted_length_is_least_code {q : ℕ} (xs : List (RawMode q)) :
    (countModes xs).result.length=Nat.clog 2 (xs.length+2) := by
  let z := (countModes xs).result
  obtain ⟨hv,hc,_⟩ := count_modes_exact xs
  change bitsValue z=1+xs.length at hv
  have hne : z≠[] := by
    intro e
    rw [e,bitsValue] at hv
    omega
  have l := canonical_lower hc hne
  change 2^(z.length-1)≤bitsValue z at l
  have u := bitsValue_lt z
  rw [hv] at l u
  have lower : z.length-1 < Nat.clog 2 (xs.length+2) :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).2 (by omega)
  have upper : Nat.clog 2 (xs.length+2) ≤ z.length :=
    (Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).2 (by omega)
  change z.length=Nat.clog 2 (xs.length+2)
  omega

/-- Each significant-bit cell advances the same width-bw ripple
counter as in the old emitter. No arithmetic logarithm is executed. -/
def emitCountLength (bw : ℕ) : List Bool → Meter (Word bw)
  | [] => zeroOrdinal bw
  | _::bs =>
    let a := emitCountLength bw bs
    let b := increment a.result
    ⟨b.result,a.steps+b.steps+3⟩

theorem emitted_count_length_is_old_writer (bw : ℕ) (bs : List Bool) :
    emitCountLength bw bs=emitOrdinal bw bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [emitCountLength,List.length_cons,emitOrdinal,ih]

structure PickedCode (bw : ℕ) where
  /-- Numeric interpretation of the exact fixed-width output word. -/
  k : ℕ
  /-- The existing inner ordinal emission debit, kept at its original consumer. -/
  write : Meter (Word bw)

def selectCode {q : ℕ} (bw : ℕ) (xs : List (RawMode q)) : Meter (PickedCode bw) :=
  let z := countModes xs
  let w := emitCountLength bw z.result
  ⟨⟨w.result.val,w⟩,z.steps⟩

theorem selected_code_is_old_word {q bw : ℕ} (xs : List (RawMode q)) (hb : 0<bw)
    (fit : Nat.clog 2 (xs.length+2)<2^bw) :
    let out := selectCode bw xs
    out.result.k=Nat.clog 2 (xs.length+2) ∧
      out.result.write=emitOrdinal bw (Nat.clog 2 (xs.length+2)) ∧
      out.result.write.steps=ordinalFee bw (Nat.clog 2 (xs.length+2)) ∧
      out.steps=(countModes xs).steps := by
  have hw : (selectCode bw xs).result.write=emitOrdinal bw (Nat.clog 2 (xs.length+2)) :=
    (emitted_count_length_is_old_writer bw _).trans (congrArg (emitOrdinal bw) (counted_length_is_least_code xs))
  have hh := emitted_ordinal_exact bw _ hb fit
  exact ⟨(congrArg (fun w : Meter (Word bw)=>w.result.val) hw).trans hh.1,
    hw,(congrArg Meter.steps hw).trans hh.2,rfl⟩

theorem actual_counter_bit_cost {q : ℕ} (xs : List (RawMode q)) (a : ℕ)
    (shaped : ∀ x∈xs,x.key.1.length=6*a ∧ x.key.2.length=6*a) :
    (countModes xs).steps ≤ 11+(24*a+6*q+21)*xs.length := by
  have hs : (xs.map (fun x=>(passMode x).steps)).sum=(24*a+6*q+5)*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := shaped x List.mem_cons_self
      have h := ih (fun y hy=>shaped y (List.mem_cons_of_mem _ hy))
      rw [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ,h,
        pass_mode_fee,hx.1,hx.2]
      omega
  have h := (count_modes_exact xs).2.2
  change (countModes xs).steps+5*ones (countModes xs).result=
    11+(xs.map (fun x=>(passMode x).steps)).sum+16*xs.length at h
  have product : (24*a+6*q+5)*xs.length+16*xs.length=(24*a+6*q+21)*xs.length := by ring
  rw [hs,Nat.add_assoc,product] at h
  omega

#print axioms bump_value
#print axioms bump_potential
#print axioms bump_canonical
#print axioms canonical_lower
#print axioms pass_mode_fee
#print axioms count_modes_from_exact
#print axioms count_modes_exact
#print axioms counted_length_is_least_code
#print axioms emitted_count_length_is_old_writer
#print axioms selected_code_is_old_word
#print axioms actual_counter_bit_cost
end J6R102NativeCodeMeter

