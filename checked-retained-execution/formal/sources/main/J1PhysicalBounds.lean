import J1PhysicalCertificate
import Mathlib.Tactic

/-! Normalize the actual physical collision/balance scores, and derive
the original MAIN finite per-cell and per-group caps from the published
feasibility inequalities. -/
namespace J1PhysicalBounds
open scoped BigOperators
open J1MainSourceCollision J1MainSourceLabels J1PhysicalHost
open J1PhysicalIncidence J1PhysicalCertificate MainClonedCNF
noncomputable section

theorem below_square_implies_load {A C : Type*} [Fintype A] [Fintype C]
    (color : A → C)
    (h : deviation color < ((Fintype.card A:ℚ)/(Fintype.card C:ℚ))^2)
    (c : C) : load color c < 2*((Fintype.card A:ℚ)/(Fintype.card C:ℚ)) := by
  classical
  let μ : ℚ := (Fintype.card A:ℚ)/(Fintype.card C:ℚ)
  let y := load color c
  have hn : 0 ≤ y := by
    unfold y load
    exact Finset.sum_nonneg (fun d _ => by
      unfold indicator
      split <;> norm_num)
  have hsq : (y-μ)^2 ≤ deviation color := by
    unfold y deviation
    exact Finset.single_le_sum (f := fun a : C => (load color a-μ)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  have hs : (y-μ)^2 < μ^2 := hsq.trans_lt h
  by_contra! ht
  have hh : 0 ≤ y*(y-2*μ) := mul_nonneg hn (sub_nonneg.mpr ht)
  nlinarith

theorem scaled_guard (a n d : ℚ) (hn : 0 ≤ n) (hd : 0 < d)
    (h : a*d^2 ≤ n) : a*n ≤ (n/d)^2 := by
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  calc
    a*n*d^2 = (a*d^2)*n := by ring
    _ ≤ n*n := mul_le_mul_of_nonneg_right h hn
    _ = n^2 := by ring

variable {B I S : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
  [Nonempty I] [Fintype S] [Nonempty S]

theorem original_caps (M : Match B) (special : I) (cfg : ConfigKey M I → S)
    (hN : 0 < Fintype.card (Vertex B))
    (hm : (10 : ℚ)*(Fintype.card (DiagonalAbundance.Draw I S):ℚ)^2 ≤
          (Fintype.card (Port (edges M)):ℚ))
    (hn : (2 : ℚ)*(Fintype.card I:ℚ)*(Fintype.card S:ℚ)^2 ≤
          (Fintype.card (Variable (Vertex B)):ℚ))
    (hs : physicalPhi M special cfg / (5*(12*(Fintype.card (Vertex B):ℚ))) +
        physicalXi M cfg / ((Fintype.card I:ℚ)*(4*(Fintype.card (Vertex B):ℚ))) < 2) :
    (∀ c, load (literalCell special (tie (edges M) Prod.fst)
        (portVar (edges M) (degree_eq_three M)) (portFactor (edges M)) cfg) c <
          2*((Fintype.card (Port (edges M)):ℚ)/(Fintype.card (DiagonalAbundance.Draw I S):ℚ))) ∧
    (∀ t g, load (fun v : Variable (Vertex B) => J1MainSourceLabels.variableWord cfg v t) g <
          2*((Fintype.card (Variable (Vertex B)):ℚ)/(Fintype.card S:ℚ))) := by
  let m : ℚ := Fintype.card (Port (edges M))
  let n : ℚ := Fintype.card (Variable (Vertex B))
  let q : ℚ := Fintype.card I
  let r : ℚ := Fintype.card S
  let D : ℚ := Fintype.card (DiagonalAbundance.Draw I S)
  have hq : 0<q := by dsimp [q]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  have hr : 0<r := by dsimp [r]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hD : 0<D := by
    dsimp [D]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (DiagonalAbundance.Draw I S))
  have hNpos : (0:ℚ) < Fintype.card (Vertex B) := by exact_mod_cast hN
  have hmpos : 0<m := by
    dsimp [m]
    rw [port_card (edges M) (degree_eq_three M)]
    positivity
  have hnpos : 0<n := by
    dsimp [n]
    rw [J1PhysicalIncidence.variables_card]
    positivity
  have hscore : physicalPhi M special cfg/(5*m)+physicalXi M cfg/(q*n)<2 := by
    simpa only [m,n,q,port_card (edges M) (degree_eq_three M),
      J1PhysicalIncidence.variables_card,Nat.cast_mul,Nat.cast_ofNat] using hs
  have hphi0 : 0 ≤ physicalPhi M special cfg := deviation_nonneg _
  have hxi0 : 0 ≤ physicalXi M cfg :=
    Finset.sum_nonneg (fun _ _ => deviation_nonneg _)
  have hphi : physicalPhi M special cfg < 10*m := by
    have hh : physicalPhi M special cfg/(5*m)<2 := by
      linarith [div_nonneg hxi0 (show 0 ≤ q*n by positivity)]
    have hb := (div_lt_iff₀ (show 0 < 5*m by positivity)).mp hh
    linarith
  have hxi : physicalXi M cfg < (2*q)*n := by
    have hh : physicalXi M cfg/(q*n)<2 := by
      linarith [div_nonneg hphi0 (show 0 ≤ 5*m by positivity)]
    have hb := (div_lt_iff₀ (show 0 < q*n by positivity)).mp hh
    linarith
  constructor
  · exact below_square_implies_load _ (hphi.trans_le (scaled_guard 10 m D hmpos.le hD hm))
  · intro t g
    have hsite :
        deviation (fun v : Variable (Vertex B) => J1MainSourceLabels.variableWord cfg v t) ≤
          physicalXi M cfg := Finset.single_le_sum (fun _ _ => deviation_nonneg _) (Finset.mem_univ t)
    exact below_square_implies_load _
      ((hsite.trans_lt hxi).trans_le (scaled_guard (2*q) n r hnpos.le hr hn)) g

#print axioms original_caps

end
end J1PhysicalBounds
