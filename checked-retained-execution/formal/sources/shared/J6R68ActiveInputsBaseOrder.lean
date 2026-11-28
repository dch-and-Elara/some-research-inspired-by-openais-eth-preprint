import J6R68ActiveInputsBaseHeight
import J6R68ActiveInputsBaseValuation

/-! The per-word stock multiplicity uses the length-encoded valuation,
truncated subtraction by lock-step list walk, and actual fixed-width
binary additions of the already computed height. -/
namespace J6R68ActiveInputs
open AOracleMachineTime AOracleMachineTimeTape A1R10 J6R22RootReadout
open J6R52FreshExterior J6ActiveSchedule J6R12CollisionBits

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
set_option maxRecDepth 2900
set_option Elab.async false

def ticks : ℕ → Meter (List Bool)
  | 0=>⟨[],2⟩
  | n+1=>let t := ticks n; ⟨false::t.result,t.steps+4⟩

theorem ticks_exact (n : ℕ) : (ticks n).result.length=n ∧ (ticks n).steps=4*n+2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨by simp [ticks,ih.1],?_⟩
    change (ticks n).steps+4=_
    rw [ih.2]
    omega

def dropTicks : List Bool → List Bool → Meter (List Bool)
  | x,[]=>⟨x,3⟩
  | [],_::_=>⟨[],3⟩
  | _::x,_::y=>let d := dropTicks x y; ⟨d.result,d.steps+4⟩

theorem drop_ticks_exact (x y : List Bool) :
    (dropTicks x y).result.length=x.length-y.length ∧
      (dropTicks x y).steps ≤ 4*y.length+3 := by
  induction y generalizing x with
  | nil => simp [dropTicks]
  | cons b y ih =>
    cases x with
    | nil => simp [dropTicks]
    | cons d x =>
      have w := ih x
      change (dropTicks x y).result.length=(x.length+1)-(y.length+1) ∧
        (dropTicks x y).steps+4 ≤ 4*(y.length+1)+3
      exact ⟨w.1.trans (by omega),by omega⟩

def accumulateTicks {q : ℕ} (base h : Word q) : List Bool → Meter (Word q)
  | []=>⟨base,2⟩
  | _::x =>
    let C := accumulateTicks base h x
    let D := addWord C.result h
    ⟨D.result,C.steps+D.steps+5⟩

theorem accumulator_exact_word_read {q : ℕ} (base h : Word q) (x : List Bool) :
    wordRead (accumulateTicks base h x).result=wordRead base+(x.length:ZMod (2^q))*wordRead h := by
  induction x with
  | nil => simp [accumulateTicks]
  | cons b x ih =>
    change wordRead (addWord (accumulateTicks base h x).result h).result=_
    rw [addWord_read,ih,List.length_cons]
    push_cast
    ring

theorem accumulator_ticks_fee {q : ℕ} (hq : 0<q) (base h : Word q) (x : List Bool) :
    (accumulateTicks base h x).steps ≤ 2+(wordArithmeticRoof q+5)*x.length := by
  induction x with
  | nil => simp [accumulateTicks]
  | cons b x ih =>
    have w := add_word_fee_le hq (accumulateTicks base h x).result h
    change (accumulateTicks base h x).steps+(addWord (accumulateTicks base h x).result h).steps+5 ≤ 2+(wordArithmeticRoof q+5)*(x.length+1)
    rw [Nat.mul_succ]
    omega

structure RawCentre (q : ℕ) where
  key : List Bool
  multiplicity : Word q

def readOrder {q : ℕ} (zero height : Word q) (axis taper bits : List Bool) :
    Meter (Option (RawCentre q)) :=
  let v := rawSignedLevel axis bits
  match v.result with
  | none=>⟨none,v.steps+3⟩
  | some level =>
    let left := dropTicks taper level
    let b := accumulateTicks zero height left.result
    let test := sameBits b.result.val zero.val
    ⟨if test.result then none else some ⟨bits,b.result⟩,v.steps+left.steps+b.steps+test.steps+7⟩

theorem read_order_is_stock {q a M u : ℕ} (hq : 0<q)
    (zero h : Word q) (z : bitsValue zero.val=0)
    (hh : bitsValue h.val=J6ActiveSchedule.height M u)
    (axis taper bits : List Bool) (ax : axis.length=a) (tap : taper.length=u) (width : bits.length=a+1)
    (hu : 0<u) (hM : u ≤ M) (fit : 4*M<2^q) :
    let t := offsetCentre a bits
    let out := readOrder zero h axis taper bits
    ((out.result.isSome=true) ↔ t∈active a M u) ∧
      (∀ row∈out.result, row.key=bits ∧ bitsValue row.multiplicity.val=order M u t) ∧
      out.steps ≤ 10*(a+1)+11+(4*a+3)+(2+(wordArithmeticRoof q+5)*u)+10*q+7 := by
  let t := offsetCentre a bits
  have grid := offset_word_in_printed_grid a bits width
  have A := signed_raw_valuation_is_exact a axis bits ax width
  dsimp only at A
  cases v : (rawSignedLevel axis bits).result with
  | none =>
    have eq : t=0 := by simpa only [v,t] using A.1
    dsimp only [readOrder]
    rw [v]
    dsimp only
    refine ⟨?_,?_,?_⟩
    · change (false=true) ↔ t∈active a M u
      rw [eq]
      simp [active]
    · simp
    · have fee := A.2
      omega
  | some level =>
    have hL : t≠0 ∧ level.length=padicValInt 2 t := by simpa only [v,t] using A.1
    let left := dropTicks taper level
    let b := accumulateTicks zero h left.result
    have leGrid : padicValInt 2 t ≤ a := by
      simpa only [sub_zero] using P1DyadicGrid.grid_difference_valuation_le grid
        (P1DyadicGrid.zero_mem_grid a) hL.1
    have leL : level.length ≤ a := hL.2 ▸ leGrid
    obtain ⟨diff,cutFee⟩ := drop_ticks_exact taper level
    change left.result.length=taper.length-level.length at diff
    change left.steps ≤ 4*level.length+3 at cutFee
    have ll : left.result.length ≤ u := diff.trans_le ((Nat.sub_le _ _).trans_eq tap)
    have real : bitsValue b.result.val=order M u t := by
      apply exact_nat_of_register_read b.result ((order_bound _ _ _ hu hM).trans_lt fit)
      rw [show wordRead b.result=wordRead zero+(left.result.length:ZMod (2^q))*wordRead h from
        accumulator_exact_word_read zero h left.result]
      change (bitsValue zero.val:ZMod (2^q))+(left.result.length:ZMod (2^q))*
        (bitsValue h.val:ZMod (2^q))=((order M u t:ℕ):ZMod (2^q))
      rw [z,hh,diff,tap,hL.2]
      unfold order
      push_cast
      ring
    have test := sameBits_exact b.result.val zero.val (b.result.property.trans zero.property.symm)
    have hT : (sameBits b.result.val zero.val).result=true↔order M u t=0 := by
      rw [test.1,real,z]
    have gridT : t∈P1DyadicGrid.grid a := grid
    have access : t∈active a M u↔0<order M u t := by
      simp [active,gridT,hL.1]
    dsimp only [readOrder]
    rw [v]
    dsimp only
    by_cases H : (sameBits b.result.val zero.val).result=true
    · rw [if_pos H]
      have full := hT.mp H
      refine ⟨?_,by simp,?_⟩
      · change (false=true) ↔ t∈active a M u
        rw [access,full]
        decide
      · have bf := (accumulator_ticks_fee hq zero h left.result).trans
          (Nat.add_le_add_left (Nat.mul_le_mul_left _ ll) 2)
        change b.steps ≤ 2+(wordArithmeticRoof q+5)*u at bf
        have cf := cutFee.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 leL) 3)
        have fe : (sameBits b.result.val zero.val).steps=10*q := test.2.trans (congrArg (10*·) b.result.property)
        have due := A.2
        change (rawSignedLevel axis bits).steps+left.steps+b.steps+
          (sameBits b.result.val zero.val).steps+7 ≤ _
        rw [fe]
        omega
    · rw [if_neg H]
      have pos : 0<order M u t := Nat.pos_of_ne_zero (fun bad=>H (hT.mpr bad))
      refine ⟨?_,?_,?_⟩
      · change (true=true) ↔ t∈active a M u
        exact ⟨fun _=>access.mpr pos,fun _=>rfl⟩
      · intro row belongs
        have he : (⟨bits,b.result⟩ : RawCentre q)=row := by simpa using belongs
        subst row
        exact ⟨rfl,real⟩
      · have bf := (accumulator_ticks_fee hq zero h left.result).trans
          (Nat.add_le_add_left (Nat.mul_le_mul_left _ ll) 2)
        change b.steps ≤ 2+(wordArithmeticRoof q+5)*u at bf
        have cf := cutFee.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 leL) 3)
        have fe : (sameBits b.result.val zero.val).steps=10*q := test.2.trans (congrArg (10*·) b.result.property)
        have due := A.2
        change (rawSignedLevel axis bits).steps+left.steps+b.steps+
          (sameBits b.result.val zero.val).steps+7 ≤ _
        rw [fe]
        omega

#print axioms drop_ticks_exact
#print axioms accumulator_exact_word_read
#print axioms read_order_is_stock
end J6R68ActiveInputs
