import J6R12CollisionMenu
import J6ActiveSchedule

/-! The first concrete base-active primitive: a paid, fixed-order
binary word enumeration of the actual signed Appendix D grid. The
offset decoder is an interpretation, not an uncharged arithmetic step
in the byte enumerator. Probe words and their order are untouched. -/
namespace J6R68ActiveInputs
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionMenu
open P1DyadicGrid J6ActiveSchedule

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 7500000
set_option maxRecDepth 2500

def offsetCentre (a : ℕ) (xs : List Bool) : ℤ :=
  (bitsValue xs : ℤ)-pow₂ a

def signedGridTape (a : ℕ) : Meter (List (List Bool)) :=
  menuMachine (a+1)

theorem offset_word_in_printed_grid (a : ℕ) (xs : List Bool) (w : xs.length=a+1) :
    offsetCentre a xs∈grid a := by
  rw [mem_grid]
  have nz : (0:ℤ) ≤ bitsValue xs := by positivity
  have h := bitsValue_lt xs
  rw [w,pow_succ] at h
  have upper : (bitsValue xs : ℤ)<pow₂ a*2 := by unfold pow₂; exact_mod_cast h
  unfold offsetCentre
  exact ⟨by omega,by omega⟩

theorem printed_grid_has_exact_word (a : ℕ) (t : ℤ) (ht : t∈grid a) :
    ∃ xs : List Bool, xs.length=a+1 ∧ offsetCentre a xs=t := by
  rw [mem_grid] at ht
  let j := (t+pow₂ a).toNat
  have nc : (j:ℤ)=t+pow₂ a := Int.toNat_of_nonneg (by omega)
  have castBound : (j:ℤ)<((2:ℕ)^(a+1) : ℤ) := by
    rw [nc]
    change t+pow₂ a < pow₂ (a+1)
    rw [pow₂_succ]
    omega
  have jfit : j<2^(a+1) := by exact_mod_cast castBound
  refine ⟨encodeBits (a+1) j,encodeBits_length _ _,?_⟩
  unfold offsetCentre
  rw [encodeBits_exact _ _ jfit,nc]
  omega

theorem paid_grid_exact (a : ℕ) :
    let tape := signedGridTape a
    tape.result=binaryMenu (a+1) ∧
      (tape.result.map (offsetCentre a)).Nodup ∧
      (tape.result.map (offsetCentre a)).toFinset=grid a ∧
      tape.steps ≤ 16*(a+2)*2^(a+1) := by
  have h := menuMachine_exact (a+1)
  change (signedGridTape a).result=binaryMenu (a+1) ∧ (signedGridTape a).steps ≤ _ at h
  dsimp only
  rw [h.1]
  refine ⟨rfl,(binary_nodup (a+1)).map_on (f:=offsetCentre a) ?_,?_,h.2⟩
  · intro x hx y hy eq
    have wx := (binary_mem (a+1) x).1 hx
    have wy := (binary_mem (a+1) y).1 hy
    apply equal_width_inj (wx.trans wy.symm)
    unfold offsetCentre at eq
    omega
  · ext t
    rw [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨xs,hx,rfl⟩
      exact offset_word_in_printed_grid a xs ((binary_mem _ _).1 hx)
    · intro ht
      obtain ⟨xs,hw,val⟩ := printed_grid_has_exact_word a t ht
      exact ⟨xs,(binary_mem _ _).2 hw,val⟩

/-- Return a unary prefix of zero lanes. No arithmetic on an unbounded
natural counter is an atomic machine operation. Drop it only when the
whole word is zero. -/
def walkToFirstOne : List Bool → Meter (Option (List Bool))
  | []=>⟨none,2⟩
  | true::_=>⟨some [],3⟩
  | false::xs =>
    let tail := walkToFirstOne xs
    ⟨tail.result.map (false::·),tail.steps+5⟩

theorem first_one_prefix_has_exact_shape (xs : List Bool) :
    match (walkToFirstOne xs).result with
    | none => xs=List.replicate xs.length false
    | some z => z=List.replicate z.length false ∧ ∃ rest : List Bool,xs=z++true::rest := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | true => exact ⟨rfl,⟨xs,rfl⟩⟩
    | false =>
      cases hz : (walkToFirstOne xs).result with
      | none =>
        rw [hz] at ih
        simp only [walkToFirstOne,hz,Option.map_none,List.length_cons,List.replicate_succ]
        exact congrArg (false::·) ih
      | some z =>
        rw [hz] at ih
        obtain ⟨ones,rest,sh⟩ := ih
        simp only [walkToFirstOne,hz,Option.map_some,List.length_cons,List.replicate_succ,
          List.cons_append]
        exact ⟨congrArg (false::·) ones,⟨rest,congrArg (false::·) sh⟩⟩

theorem actual_first_one_scan_fee (xs : List Bool) :
    (walkToFirstOne xs).steps ≤ 5*xs.length+3 := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    cases b with
    | true => simp [walkToFirstOne]
    | false =>
      change (walkToFirstOne xs).steps+5 ≤ 5*(xs.length+1)+3
      omega

#print axioms offset_word_in_printed_grid
#print axioms paid_grid_exact
#print axioms first_one_prefix_has_exact_shape
#print axioms actual_first_one_scan_fee
end J6R68ActiveInputs
