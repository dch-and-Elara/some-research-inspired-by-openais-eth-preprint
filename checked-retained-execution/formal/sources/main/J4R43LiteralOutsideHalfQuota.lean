import J4R43LiteralOutsideSharpCensus
import J4R43LiteralOutsideDeterministicSupply

/-! The manuscript's stronger per-cell quantitative sentence:
the very same deterministic marking leaves at least c H_pad/2
distinct matching edges in every actual cell, before seating. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open P11FullPacking J6R10Repack
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5500000

variable {E A B G : Type} [Fintype E] [Fintype G] [LinearOrder G] [Nonempty G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (pin : E)

theorem actual_retained_half_pad (d : ℕ)
    (dr : ∀ v : A,Nat.card {e : E//N.row e=v}≤d)
    (dc : ∀ v : B,Nat.card {e : E//N.col e=v}≤d)
    (high : ∀ c : Cell (Fin a) G,
      3*fullLoad P+4*starWidth d≤4*Nat.card (InputCell P c))
    (large : 64*(reciprocal d)^2*(starWidth d)^2*Nat.card E≤(fullLoad P)^2) :
    ∀ c : Cell (Fin a) G,
      (fullLoad P:ℚ)/(2*(reciprocal d:ℚ))≤
        (Nat.card (RetainedAt P pin (deterministic_source_marks P pin) c):ℚ) := by
  let H := fullLoad P
  let R := reciprocal d
  let D := starWidth d
  let margin : ℚ := (H:ℚ)/(4*(R:ℚ))
  have Rn : 0<R := by unfold R reciprocal; positivity
  have Rq : (0:ℚ)<R := by exact_mod_cast Rn
  have nonneg : 0≤margin := by dsimp [margin]; positivity
  have bound : (4:ℚ)*(Nat.card E:ℚ)*((2*d-1)*(2*d-1):ℕ)≤margin^2 := by
    have src : (64:ℚ)*(R:ℚ)^2*(D:ℚ)^2*(Nat.card E:ℚ)≤(H:ℚ)^2 := by exact_mod_cast large
    dsimp only [margin]
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : (0:ℚ)<(4*(R:ℚ))^2)).mpr
    push_cast
    change (4:ℚ)*(Nat.card E:ℚ)*((D:ℚ)*(D:ℚ))*(4*(R:ℚ))^2≤_
    calc
      _=(64:ℚ)*(R:ℚ)^2*(D:ℚ)^2*(Nat.card E:ℚ) := by ring
      _≤_ := src
  have surv : (1/2:ℚ)^D=1/(R:ℚ) := by
    rw [div_pow,one_pow]
    simp only [R,reciprocal,D,starWidth,Nat.cast_pow,Nat.cast_ofNat]
  intro c
  have erase := input_minus_closed_pin P pin c
  have size := literal_closed_count N d dr dc pin
  have hh := high c
  have eligible : 3*H≤4*Nat.card (EligibleAt P pin c) := by
    change 3*H+4*D≤4*Nat.card (InputCell P c) at hh
    change (close N pin).card≤D at size
    omega
  have val : (3:ℚ)*(H:ℚ)≤4*(Nat.card (EligibleAt P pin c):ℚ) := by exact_mod_cast eligible
  have m := mean_in_actual_cell P pin c D (literal_block_count N d dr dc pin)
  rw [surv,mul_one_div] at m
  have b := (abs_le.mp (actual_marks_mean_margin P pin d dr dc margin nonneg bound c)).1
  have target : (H:ℚ)/(2*(R:ℚ))+margin≤
      (Nat.card (EligibleAt P pin c):ℚ)/(R:ℚ) := by
    have eq : (H:ℚ)/(2*(R:ℚ))+margin= (3*(H:ℚ))/(4*(R:ℚ)) := by
      dsimp only [margin]
      field_simp
      ring
    rw [eq]
    apply (div_le_div_iff₀ (by positivity : (0:ℚ)<4*(R:ℚ)) Rq).mpr
    have p := mul_le_mul_of_nonneg_right val Rq.le
    nlinarith only [p]
  have es := target.trans m
  linarith

theorem actual_half_from_printed_variance (d : ℕ)
    (dr : ∀ v : A,Nat.card {e : E//N.row e=v}≤d)
    (dc : ∀ v : B,Nat.card {e : E//N.col e=v}≤d)
    (copies : P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)))
    (var : varianceScore (declaredCell N P.rowLabel P.colLabel)≤6*(Nat.card E:ℚ))
    (rough : 1536*(nCells (a:=a) (G:=G))^2≤Nat.card E)
    (mesh : 16*2^a*nCells (a:=a) (G:=G)≤Nat.card E)
    (small : 32*starWidth d*nCells (a:=a) (G:=G)≤Nat.card E)
    (large : 64*(reciprocal d)^2*(starWidth d)^2*(nCells (a:=a) (G:=G))^2≤Nat.card E) :
    ∀ c : Cell (Fin a) G,
      (fullLoad P:ℚ)/(2*(reciprocal d:ℚ))≤
        (Nat.card (RetainedAt P pin (deterministic_source_marks P pin) c):ℚ) := by
  obtain ⟨_,h,s⟩ := actual_census_for_half_retention P d copies var rough mesh small large
  exact actual_retained_half_pad P pin d dr dc h s

#print axioms actual_retained_half_pad
#print axioms actual_half_from_printed_variance
end
end J4R43LiteralOutside

