import V8CapacityUnifiedScalarIndex
import V8CapacityUnifiedWidth
import V8CapacityWidthRank

/-! S2 upper bound for the literal public scalar classes. The remainder
module concerns evaluations on the actual class, not polynomial
coefficientwise divisibility. The decoder coefficients are unrestricted. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open V8CapacityDigits V8CapacityMonicBasis V8CapacityCRTJet
open V8CapacityWidthUpper V8CapacityWidthRank
open MvPolynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

variable {O H : Type*} [CommRing O] [IsDomain O] [Fintype H]
variable {π : O} {q : ℕ} (D : Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (s : PublicClass (O:=O) (H:=H))

def vanish (π : O) (P : ℕ) (s : PublicClass (O:=O) (H:=H)) :
    Submodule O (MvPolynomial H O) where
  carrier := { f | ∀ u, permitted π s u → π^P∣MvPolynomial.eval u f }
  zero_mem' u _ := by rw [map_zero]; exact dvd_zero _
  add_mem' hf hg u hu := by rw [map_add]; exact dvd_add (hf u hu) (hg u hu)
  smul_mem' a f hf u hu := by
    rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C]
    exact dvd_mul_of_dvd_right (hf u hu) _

def activeSpan (P : ℕ) : Submodule O (MvPolynomial H O) :=
  Submodule.span O (Set.range (fun j : S2Index q P s.depth => phi D hq s (indexDegree j)))

include D hq hq₂ h0 hπ in
theorem remainder_cover (P : ℕ) (C : MvPolynomial H O) :
    C∈activeSpan D hq s P ⊔ vanish π P s := by
  obtain ⟨c,hc⟩ := phi_expand D hq s C.totalDegree C le_rfl
  rw [← hc]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  by_cases hi : weight q s.depth (rowDegree i)<P
  · have ha : phi D hq s (rowDegree i)∈activeSpan D hq s P := by
      apply Submodule.subset_span
      refine ⟨indexFor q P hq s.depth (rowDegree i) hi,?_⟩
      exact congrArg (phi D hq s) (indexFor_degree q P hq s.depth (rowDegree i) hi)
    exact (show activeSpan D hq s P≤activeSpan D hq s P⊔vanish π P s from le_sup_left) ha
  · have hv : phi D hq s (rowDegree i)∈vanish π P s := by
      intro u hu
      exact (pow_dvd_pow π (Nat.le_of_not_gt hi)).trans
        (phi_eval_divisibility D hq hq₂ h0 hπ s (rowDegree i) u hu)
    exact (show vanish π P s≤activeSpan D hq s P⊔vanish π P s from le_sup_right) hv

include D hq hq₂ h0 hπ in
/-- One finite active polynomial plus a truly invisible remainder for
every receiver polynomial, including arbitrarily high input degree. -/
theorem finite_reduction (P : ℕ) (C : MvPolynomial H O) :
    ∃ coeff : S2Index q P s.depth → O,
      ∃ rem : vanish π P s,
        C=(∑ i : S2Index q P s.depth, coeff i • phi D hq s (indexDegree i))+rem.val := by
  obtain ⟨a,ha,err,herr,h⟩ := Submodule.mem_sup.mp (remainder_cover D hq hq₂ h0 hπ s P C)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp ha
  refine ⟨c,⟨err,herr⟩,?_⟩
  rw [hc,h]

variable {K X Y : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable (L p : ℕ)

local notation "P" => (L+p)
local notation "I" => S2Index q P s.depth

def scalarOutput (π : O) (L : ℕ) (u : H → O) (C : MvPolynomial H O) : K :=
  algebraMap O K (MvPolynomial.eval u C)/(algebraMap O K (π^L))

include D hq hq₂ h0 hπ in
theorem S2_separated (u : X → H → O) (hu : ∀ x, permitted π s (u x))
    (C : Y → MvPolynomial H O) :
    ∃ l : X → I → K, ∃ r : I → Y → K,
      ∀ x y, ∃ e : O,
        scalarOutput π L (u x) (C y) - (∑ i : I, l x i*r i y)=algebraMap O K (π^p*e) := by
  choose c rem hc using fun y => finite_reduction D hq hq₂ h0 hπ s P (C y)
  let g (y : Y) := ∑ i : I, c y i • phi D hq s (indexDegree i)
  let l (x : X) (i : I) : K := scalarOutput π L (u x) (phi D hq s (indexDegree i))
  let r (i : I) (y : Y) : K := algebraMap O K (c y i)
  refine ⟨l,r,fun x y => ?_⟩
  have hv : π^P∣MvPolynomial.eval (u x) (C y)-MvPolynomial.eval (u x) (g y) := by
    rw [hc y]
    change π^P ∣ MvPolynomial.eval (u x) (g y+(rem y).val)-MvPolynomial.eval (u x) (g y)
    rw [map_add,add_sub_cancel_left]
    exact (rem y).property _ (hu x)
  have hh := divided_diff (K:=K) hπ L p (MvPolynomial.eval (u x) (C y))
    (MvPolynomial.eval (u x) (g y)) hv
  have he : (∑ i : I, l x i*r i y)=scalarOutput π L (u x) (g y) := by
    unfold scalarOutput g
    simp only [MvPolynomial.smul_eq_C_mul,map_sum,map_mul,MvPolynomial.eval_C,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    unfold l scalarOutput r
    ring
  rw [he]
  exact hh

variable [Fintype X] [Fintype Y]

include D hq hq₂ h0 hπ in
theorem S2_fractional_upper (u : X → H → O) (hu : ∀ x, permitted π s (u x))
    (C : Y → MvPolynomial H O) :
    ∃ A : Matrix X Y K, A.rank≤Nat.card (S2Raw q P s.depth) ∧
      ∀ x y, ∃ e : O, scalarOutput π L (u x) (C y)-A x y=algebraMap O K (π^p*e) := by
  obtain ⟨l,r,h⟩ := S2_separated (K:=K) D hq hq₂ h0 hπ s L p u hu C
  refine ⟨Matrix.of (fun x y => ∑ i : I, l x i*r i y),?_ ,h⟩
  rw [← s2_is_exact_count q P hq s.depth]
  exact separated_sum_rank l r

variable [IsPrincipalIdealRing O]

include D hq hq₂ h0 hπ in
theorem S2_integral_upper (u : X → H → O) (hu : ∀ x, permitted π s (u x))
    (C : Y → MvPolynomial H O) (target : Matrix X Y O)
    (correct : ∀ x y, π^P∣MvPolynomial.eval (u x) (C y)-π^L*target x y) :
    ∃ A : Matrix X Y O, A.map (coeffMod O π p)=target.map (coeffMod O π p) ∧
      (A.map (algebraMap O K)).rank≤Nat.card (S2Raw q P s.depth) := by
  obtain ⟨l,r,h⟩ := S2_separated (K:=K) D hq hq₂ h0 hπ s L p u hu C
  have hd : algebraMap O K (π^L)≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr (pow_ne_zero _ hπ)
  have hc (x : X) (y : Y) : ∃ e : O,
      algebraMap O K (target x y)-(∑ i : I, l x i*r i y)=algebraMap O K (π^p*e) := by
    obtain ⟨e,he⟩ := h x y
    obtain ⟨d,hd'⟩ := divided_diff (K:=K) hπ L p (MvPolynomial.eval (u x) (C y))
      (π^L*target x y) (correct x y)
    rw [map_mul, mul_comm (algebraMap O K (π^L)),mul_div_cancel_right₀ _ hd] at hd'
    change scalarOutput π L (u x) (C y)-algebraMap O K (target x y)=_ at hd'
    refine ⟨e-d,?_⟩
    rw [mul_sub,map_sub]
    linear_combination he-hd'
  obtain ⟨A,hA,hRank⟩ := integral_congruent_low_rank π p target l r hc
  rw [← s2_is_exact_count q P hq s.depth]
  exact ⟨A,hA,hRank⟩

include D hq hq₂ h0 hπ in
theorem S2_residue_width (u : X → H → O) (hu : ∀ x, permitted π s (u x))
    (C : Y → MvPolynomial H O) (target : Matrix X Y O)
    (correct : ∀ x y, π^P∣MvPolynomial.eval (u x) (C y)-π^L*target x y) :
    ∃ d≤Nat.card (S2Raw q P s.depth),
      V8CapacityUnified.factors π p (fun y x => coeffMod O π p (target x y)) d := by
  obtain ⟨A,hA,hr⟩ := S2_integral_upper (K:=FractionRing O) D hq hq₂ h0 hπ s L p u hu C target correct
  obtain ⟨n,hn,a,b,hb⟩ := residue_factor_of_krank (K:=FractionRing O) π p A
  exact ⟨n,hn.trans hr,a,b,hA.symm.trans hb⟩

#print axioms remainder_cover
#print axioms finite_reduction
#print axioms S2_separated
#print axioms S2_fractional_upper
#print axioms S2_integral_upper
#print axioms S2_residue_width
end
end V8CapacityUnified.Scalar
