import A1R9Framing
import A1R9Physical

/-! Polynomial envelope in explicit scalar tape parameters. The cost of
each original truth-table menu is bounded here by the stated arity cap.
For fixed source degree that cap is constant. This is not a bound in
the bit length of a succinct graph/query header alone. -/

namespace A1R9
open AOracleMachineTimeZero AOracleSuccinct

def tapeScale {r c m delta p : ℕ} (br bc bm bq s : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) : ℕ :=
  1+r+c+m+delta+p+br+bc+bm+bq+s+L.rows.length+L.cols.length+2^delta

set_option maxHeartbeats 500000 in
theorem witnessBudget_poly {r c m delta p : ℕ} (br bc bm bq s : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) :
    r*(12*(bm+1)+4)+witnessBudget br bc bm bq s L+2 ≤ 400*(tapeScale br bc bm bq s L)^4 := by
  let S := tapeScale br bc bm bq s L
  let T := 1+r+c+m+delta+p+br+bc+bm+bq+s+L.rows.length+L.cols.length
  have hTS : T≤S := Nat.le_add_right _ _
  have hS : 1≤S := (show 1≤T by dsimp [T]; omega).trans hTS
  have hp : p+1≤S := (show p+1≤T by dsimp [T]; omega).trans hTS
  have hm : m+1≤S := (show m+1≤T by dsimp [T]; omega).trans hTS
  have herr : r≤S := (show r≤T by dsimp [T]; omega).trans hTS
  have hcol : c≤S := (show c≤T by dsimp [T]; omega).trans hTS
  have ht : delta≤S := (show delta≤T by dsimp [T]; omega).trans hTS
  have hu : 2^delta≤S := Nat.le_add_left _ _
  have hs : s≤S := (show s≤T by dsimp [T]; omega).trans hTS
  have hbr : br≤S := (show br≤T by dsimp [T]; omega).trans hTS
  have hbc : bc≤S := (show bc≤T by dsimp [T]; omega).trans hTS
  have hbm : bm≤S := (show bm≤T by dsimp [T]; omega).trans hTS
  have hbq : bq≤S := (show bq≤T by dsimp [T]; omega).trans hTS
  have hbm1 : bm+1≤S := (show bm+1≤T by dsimp [T]; omega).trans hTS
  have hr : L.rows.length≤S := (show L.rows.length≤T by dsimp [T]; omega).trans hTS
  have hc : L.cols.length≤S := (show L.cols.length≤T by dsimp [T]; omega).trans hTS
  have tb (n b : ℕ) (hn : n≤S) (hb : b≤S) :
      tensorBudget n delta b≤S*((10*S+4)*S+2)+(10*S+4)*S+4 := by
    unfold tensorBudget
    gcongr
  have hPick : pickedBudget c bc p s≤
      S+S*((10*S+4)*S+12*S+4)+16*S^2+15*S+4 := by
    have hp' : p≤S := by omega
    unfold pickedBudget
    gcongr
  have hSelect : selectBudget m bm c bc p s≤ S*(10*S+4+(S*(S+S+2)+S+3))+
      (S+S*((10*S+4)*S+12*S+4)+16*S^2+15*S+4)+3 := by
    have hp' : p≤S := by omega
    unfold selectBudget
    gcongr
  have hStage : rowStageBudget m bm c bc p s≤ S*(10*S+4+(S*(S+S+2)+S+3))+
      (S+S*((10*S+4)*S+12*S+4)+16*S^2+15*S+4)+3+16*S^2+6 := by
    unfold rowStageBudget
    gcongr
  have hCounter : counterBudget r bm bq+2≤S+S*(10*S+12*S+6)+10*S+4 := by
    unfold counterBudget
    have hh : bq+r*(10*bm+12*bq+6)+10*bq ≤ S+S*(10*S+12*S+6)+10*S := by
      gcongr
    omega
  have hRaw : r*(12*(bm+1)+4)+witnessBudget br bc bm bq s L+2 ≤
      S*(12*S+4)+
      (2*S*(S*((10*S+4)*S+2)+(10*S+4)*S+4)+S+
      S*(S*(10*S+4+(S*(S+S+2)+S+3))+
        (S+S*((10*S+4)*S+12*S+4)+16*S^2+15*S+4)+3+16*S^2+6)+
      S*(S+S*(10*S+12*S+6)+10*S+4)+10*S+8)+2 := by
    have hm' : m≤S := by omega
    have hp' : p≤S := by omega
    have ht1 := tb r br herr hbr
    have ht2 := tb c bc hcol hbc
    let T := S*((10*S+4)*S+2)+(10*S+4)*S+4
    have ht12 : L.rows.length*tensorBudget r delta br+L.cols.length*tensorBudget c delta bc≤2*S*T := by
      calc
        _ ≤ S*T+S*T := Nat.add_le_add (Nat.mul_le_mul hr ht1) (Nat.mul_le_mul hc ht2)
        _ = _ := by ring
    unfold witnessBudget
    gcongr
  refine hRaw.trans ?_
  have h1 : S≤S^4 := by simpa using Nat.pow_le_pow_right hS (show 1≤4 by decide)
  have h2 : S^2≤S^4 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S^3≤S^4 := Nat.pow_le_pow_right hS (by decide)
  change _ ≤ 400*S^4
  nlinarith

open AOracleWitness AOracleThreshold AOracleSuccinctPacket

/-- Complete compositional scope of the scalar result: supplied signed
root coefficient tapes, unaltered actual finite-bit guesses (invalid
codes rejected), and explicit per-guess cost. No correctness or cost
assumption about the counting oracle appears here. -/
theorem physicalBitMachine_count_and_cost {r c m packets G a i delta p : ℕ}
    (rows : List (BoolTensor r delta)) (columns : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) (t : ℤ) (z : ZMod (2^p))
    (beta : Fin m →₀ ℕ) (br bc bm bq : ℕ)
    (hp : 0<p) (hq : 0<bq) (hr : r≤2^br) (hc : c≤2^bc)
    (hm : m+1≤2^bm) (hrq : r<2^bq) (hb : ∀ k, beta k<2^bq) :
    let L := scalarPhysical rows columns row col modes t z
    let M := scalarBitMachine br bc bm bq L beta
    (countVerify (fun code => (M code).result) : ZMod (2^p)) =
      MvPolynomial.coeff beta (rootPolynomial (rootTerms L)) ∧
    ∀ code, (M code).steps≤400*(tapeScale br bc bm bq c L)^4 := by
  let L := scalarPhysical rows columns row col modes t z
  obtain ⟨hL,hM⟩ := physicalRecipe_lengths rows columns row col modes t z
  refine ⟨scalarBitMachine_count br bc bm bq c hp hq hr hc hm hrq L beta hb hL hM,?_⟩
  intro code
  exact (scalarBitMachine_model br bc bm bq c hp hq hr hc hm hrq L beta hb hL hM code).2.trans
    (witnessBudget_poly br bc bm bq c L)

#print axioms witnessBudget_poly
#print axioms physicalBitMachine_count_and_cost
end A1R9
