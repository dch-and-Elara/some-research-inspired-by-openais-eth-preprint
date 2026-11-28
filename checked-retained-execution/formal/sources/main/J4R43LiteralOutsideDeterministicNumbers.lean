import J4R43LiteralOutsideTiedChart
import J4R43LiteralOutsideDeterministicSupply

/-! A finite form of the manuscript's n_cell~H and H≫√M
hypotheses. Both checks are on the actual immutable graph-only chart;
they do not mention a selected matching or a register value. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open P11FullPacking J6R10Repack
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3800000
variable {E A B G : Type} [Fintype E] [Fintype G] [LinearOrder G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (pin : E)

def deterministic_printed_band_from_real_cell_loads (d : ℕ)
    (hcopy : 0<P.copies)
    (row : ∀ b : A,Nat.card {e : E//N.row e=b}≤d)
    (col : ∀ b : B,Nat.card {e : E//N.col e=b}≤d)
    (loaded : ∀ c : Cell (Fin a) G,
      fullLoad P+2*starWidth d≤2*Nat.card (InputCell P c))
    (size : 64*(reciprocal d)^2*(starWidth d)^2*Nat.card E≤(fullLoad P)^2) :
    BandSupply P (printedBand a d) pin := by
  let H := fullLoad P
  let R := reciprocal d
  let D := starWidth d
  let h := printedBand a d
  have hn : (0:ℕ)<R := by unfold R reciprocal; positivity
  have hr : (0:ℚ)<R := by exact_mod_cast hn
  let m : ℚ := H/(4*(R:ℚ))
  have hm : 0≤m := by dsimp [m]; positivity
  have big : (64:ℚ)*(R:ℚ)^2*(D:ℚ)^2*(Nat.card E:ℚ)≤(H:ℚ)^2 := by
    exact_mod_cast size
  have varFit : 4*(Nat.card E:ℚ)*(D*D:ℕ)≤m^2 := by
    dsimp only [m]
    rw [div_pow]
    have p : (0:ℚ)<(4*(R:ℚ))^2 := by positivity
    apply (le_div_iff₀ p).mpr
    push_cast
    calc
      _ = (64:ℚ)*(R:ℚ)^2*(D:ℚ)^2*(Nat.card E:ℚ) := by ring
      _ ≤ _ := big
  have hPlan : h*(8*R)≤2^a := Nat.div_mul_le_self _ _
  have hCut : (2*h*P.copies)*(4*R)≤H := by
    calc
      _ = P.copies*(h*(8*R)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hPlan
  have used : ((2*h*P.copies:ℕ):ℚ)≤m := by
    unfold m
    apply (le_div_iff₀ (by positivity : (0:ℚ)<4*(R:ℚ))).mpr
    exact_mod_cast hCut
  have cR : (1/2:ℚ)^D=1/(R:ℚ) := by
    rw [div_pow,one_pow]
    simp only [R,reciprocal,D,starWidth,Nat.cast_pow,Nat.cast_ofNat]
  have enough (c : Cell (Fin a) G) :
      ((2*h*P.copies:ℕ):ℚ)+m≤(Nat.card (EligibleAt P pin c):ℚ)*(1/2:ℚ)^D := by
    have count := input_minus_closed_pin P pin c
    have closed := literal_closed_count N d row col pin
    have hL := loaded c
    have req : H≤2*Nat.card (EligibleAt P pin c) := by
      change (close N pin).card≤D at closed
      change H+2*D≤2*Nat.card (InputCell P c) at hL
      omega
    have e : (H:ℚ)≤2*(Nat.card (EligibleAt P pin c):ℚ) := by exact_mod_cast req
    rw [cR]
    calc
      _ ≤ m+m := add_le_add_right used _
      _ = (H:ℚ)/(2*(R:ℚ)) := by dsimp only [m]; field_simp; ring
      _ ≤ _ := by
        rw [mul_one_div]
        apply (div_le_div_iff₀ (by positivity : 0<2*(R:ℚ)) hr).mpr
        nlinarith
  exact deterministic_original_matching_supply P pin h d hcopy row col m hm varFit enough

def deterministic_post_transpose_quota (d : ℕ)
    (hc : 0<P.copies) (left : ∀ v : A,Nat.card {e : E//N.row e=v}≤d)
    (right : ∀ v : B,Nat.card {e : E//N.col e=v}≤d)
    (loaded : ∀ c : Cell (Fin a) G, fullLoad P+2*starWidth d≤2*Nat.card (InputCell P c))
    (scale : 64*(reciprocal d)^2*(starWidth d)^2*Nat.card E≤(fullLoad P)^2) :
    BandSupply (transposePacking P) (printedBand a d) pin := by
  apply deterministic_printed_band_from_real_cell_loads (transposePacking P) pin d hc right left
  · intro c
    rw [equal_transposed_census]
    exact loaded _
  · exact scale

#print axioms deterministic_printed_band_from_real_cell_loads
#print axioms deterministic_post_transpose_quota
end
end J4R43LiteralOutside

