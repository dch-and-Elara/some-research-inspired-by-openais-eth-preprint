import P5P3RootWindow
import HermiteLossDenominator

/-! §7 Paper 5 finite profile selection. Every native node has its own
integer order, with order zero represented as omission. The tapered
construction is the paper's choice, not an assumption on all profiles. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

abbrev Profile (u : ℕ) := (Paper5.P3.rootNodes u) → ℕ

def admissibleOrders (M u : ℕ) (q : Profile u) : Prop :=
  ∀ t, q t ≤ taper u (sourceH M u) (level t.val)

def taperProfile (u v H : ℕ) : Profile u :=
  fun t => taper v H (level t.val)

def orderMass (u : ℕ) (q : Profile u) : ℕ := ∑ t,q t

def adaptedHeight (M u : ℕ) : ℕ := 4*sourceH M u/3

def adaptedDepth (M u : ℕ) : ℕ :=
  (M+adaptedHeight M u-1)/adaptedHeight M u+2

theorem taperProfile_fits {M u v H : ℕ} (hv : v≤u) (hH : sourceH M u≤H)
    (hmass : H*v≤sourceH M u*u) : admissibleOrders M u (taperProfile u v H) := by
  intro t
  let i := level t.val
  change H*(v-i) ≤ sourceH M u*(u-i)
  by_cases h : i≤v
  · have hui : i≤u := h.trans hv
    have h1 : H*(v-i)+H*i=H*v := by rw [←Nat.mul_add,Nat.sub_add_cancel h]
    have h2 : sourceH M u*(u-i)+sourceH M u*i=sourceH M u*u := by
      rw [←Nat.mul_add,Nat.sub_add_cancel hui]
    have h3 := Nat.mul_le_mul_right i hH
    omega
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt (lt_of_not_ge h))]

theorem adapted_height_arithmetic (M u : ℕ) :
    sourceH M u≤adaptedHeight M u ∧ 6*adaptedHeight M u≤8*sourceH M u := by
  unfold adaptedHeight
  constructor
  · apply (Nat.le_div_iff_mul_le (by decide : 0<3)).mpr
    omega
  · have h := Nat.div_mul_le_self (4*sourceH M u) 3
    omega

theorem adapted_profile_parameters {M u : ℕ} (hu : 8≤u) (hM : u≤M) :
    0<adaptedHeight M u ∧ 2≤adaptedDepth M u ∧ adaptedDepth M u≤u ∧
      M+2*adaptedHeight M u≤adaptedHeight M u*adaptedDepth M u ∧
      adaptedHeight M u*adaptedDepth M u≤sourceH M u*u := by
  let h := sourceH M u
  let H := adaptedHeight M u
  let v := adaptedDepth M u
  change 0<H ∧ 2≤v ∧ v≤u ∧ M+2*H≤H*v ∧ H*v≤h*u
  have hpos : 0<h := by
    have hc := h_cover M u (by omega)
    change 3*M≤h*u at hc
    by_contra hn
    have hz : h=0 := by omega
    rw [hz,zero_mul] at hc
    omega
  obtain ⟨hH,h6⟩ := adapted_height_arithmetic M u
  change h≤H at hH
  have hH0 : 0<H := hpos.trans_le hH
  have hreq : 3*M≤h*u := h_cover M u (by omega)
  have hhu : h*u≤4*M := h_upper M u hM
  have h4 : 4*h≤2*M := by
    have hm := Nat.mul_le_mul_left h hu
    omega
  have hcv : M≤((M+H-1)/H)*H := J9PrintedSchedule.le_roundup_mul M H hH0
  have huv : ((M+H-1)/H)*H≤M+H-1 := Nat.div_mul_le_self _ _
  have hveq : H*v=((M+H-1)/H)*H+2*H := by
    change H*((M+H-1)/H+2)=_
    ring
  have h3H : 3*H≤4*h := by change 6*H≤8*h at h6; omega
  have hvhu : H*v≤h*u := by omega
  have hvu : v≤u := by
    by_contra hv
    have ht := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hv) hH0
    have hh := Nat.mul_le_mul_right u hH
    omega
  have hv2 : 2≤v := by
    change 2≤(M+H-1)/H+2
    exact Nat.le_add_left _ _
  exact ⟨hH0,hv2,hvu,by omega,hvhu⟩

theorem adapted_profile_admissible {M u : ℕ} (hu : 8≤u) (hM : u≤M) :
    admissibleOrders M u (taperProfile u (adaptedDepth M u) (adaptedHeight M u)) := by
  obtain ⟨_,_,hv,_,hfit⟩ := adapted_profile_parameters hu hM
  exact taperProfile_fits hv (adapted_height_arithmetic M u).1 hfit

def shellWeightSum (a v : ℕ) : ℕ :=
  ∑ i∈Finset.range v, (2:ℕ)^(a-i)

def shellTaperMass (a v : ℕ) : ℕ :=
  ∑ i∈Finset.range v, (2:ℕ)^(a-i)*(v-i)

theorem shellWeightSum_closed (a v : ℕ) (hv : v≤a+1) :
    shellWeightSum a v + 2^(a+1-v) = 2^(a+1) := by
  induction v with
  | zero => simp [shellWeightSum]
  | succ v ih =>
    have hle : v≤a := by omega
    have h1 := ih (by omega)
    have h2 : 2^(a+1-v) = (2:ℕ)^(a-v)*2 := by
      rw [show a+1-v=(a-v)+1 by omega,pow_succ]
    have h3 : a+1-(v+1)=a-v := by omega
    have hs : shellWeightSum a (v+1) = shellWeightSum a v + 2^(a-v) := by
      simp only [shellWeightSum,Finset.sum_range_succ]
    rw [hs,h3]
    rw [h2] at h1
    calc
      shellWeightSum a v + 2^(a-v) + 2^(a-v) = shellWeightSum a v + 2^(a-v)*2 := by ring
      _ = _ := h1

theorem shellTaperMass_succ (a v : ℕ) :
    shellTaperMass a (v+1) = shellTaperMass a v + shellWeightSum a (v+1) := by
  unfold shellTaperMass shellWeightSum
  rw [Finset.sum_range_succ,Finset.sum_range_succ (f:=fun i => (2:ℕ)^(a-i))]
  rw [show v+1-v=1 by omega,mul_one]
  have he : (∑ j∈Finset.range v,(2:ℕ)^(a-j)*(v+1-j)) =
      (∑ j∈Finset.range v,(2:ℕ)^(a-j)*(v-j)) + ∑ j∈Finset.range v,(2:ℕ)^(a-j) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hv : j < v := Finset.mem_range.mp hj
    rw [show v+1-j=(v-j)+1 by omega,Nat.mul_add,mul_one]
  rw [he,add_assoc]

theorem shellTaperMass_closed (a v : ℕ) (hv : v≤a+1) :
    shellTaperMass a v + 2^(a+1) = v*2^(a+1)+2^(a+1-v) := by
  induction v with
  | zero => simp [shellTaperMass]
  | succ v ih =>
    have h0 := ih (by omega)
    have h1 := shellWeightSum_closed a (v+1) hv
    have hp : (2:ℕ)^(a+1-v) = 2^(a+1-(v+1))*2 := by
      rw [←pow_succ]
      congr 1
      omega
    rw [shellTaperMass_succ,Nat.succ_mul]
    rw [hp] at h0
    omega

theorem taperProfile_mass (u v H : ℕ) (hv : v≤u) :
    orderMass u (taperProfile u v H) = H*shellTaperMass (2*u) v := by
  unfold orderMass taperProfile
  rw [← Finset.sum_subtype (Paper5.P3.rootNodes u) (fun x => Iff.rfl)
    (fun t => taper v H (level t))]
  have hroot : Paper5.P3.rootNodes u ⊆ (grid (2*u)).erase 0 := by
    intro t ht
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp ht).2.1,(Finset.mem_filter.mp ht).1⟩
  have hs : (∑ t∈Paper5.P3.rootNodes u,taper v H (level t)) =
      ∑ t∈(grid (2*u)).erase 0,taper v H (level t) := by
    apply Finset.sum_subset hroot
    intro t ht hnot
    have hl : u≤level t := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase ht,
        Finset.ne_of_mem_erase ht,Nat.lt_of_not_ge hn⟩)
    simp [taper,Nat.sub_eq_zero_of_le (hv.trans hl)]
  rw [hs,histogram_sum]
  have hz : (∑ j∈Finset.range v,(2:ℕ)^(2*u-j)*taper v H j) =
    ∑ j∈Finset.range (2*u+1),(2:ℕ)^(2*u-j)*taper v H j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have h := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
    simp [taper,Nat.sub_eq_zero_of_le h]
  rw [←hz,shellTaperMass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold taper
  ring

/-- Exact natural-number form of (P.4), before dropping the positive tail. -/
theorem taperProfile_mass_closed (u v H : ℕ) (hv : v≤u) :
    orderMass u (taperProfile u v H) + H*2^(2*u+1) =
      H*(v*2^(2*u+1)+2^(2*u+1-v)) := by
  rw [taperProfile_mass u v H hv,←Nat.mul_add,shellTaperMass_closed (2*u) v (by omega)]

theorem taperProfile_degree_slack (M u v H : ℕ) (hv : v≤u) (cover : M+2*H≤H*v) :
    2*H*2^(2*u)+M ≤ orderMass u (taperProfile u v H) - Paper5.P3.printedDegree u M := by
  let L := (2:ℕ)^(2*u)
  let S := orderMass u (taperProfile u v H)
  have he := taperProfile_mass_closed u v H hv
  rw [pow_succ] at he
  change S+H*(L*2) = H*(v*(L*2)+2^(2*u+1-v)) at he
  have hS1 : (M+2*H)*(L*2) ≤ (H*v)*(L*2) := Nat.mul_le_mul_right _ cover
  have h1 : (M+2*H)*(L*2)=2*M*L+2*H*L+2*H*L := by ring
  have h2 : S+2*H*L=H*v*(L*2)+H*2^(2*u+1-v) := by
    calc
      S+2*H*L = S+H*(L*2) := by ring
      _ = _ := he.trans (by ring)
  have hs2 : 2*M*L+2*H*L≤S := by
    rw [h1] at hS1
    omega
  have hL : 0 < L := by dsimp [L]; positivity
  have hd : Paper5.P3.printedDegree u M+M=2*M*L := by
    unfold Paper5.P3.printedDegree
    change M*(2*L-1)+M=2*M*L
    calc
      M*(2*L-1)+M = M*((2*L-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel (by omega)]; ring
  change 2*H*L+M≤S-Paper5.P3.printedDegree u M
  omega

#print axioms taperProfile_fits
#print axioms adapted_height_arithmetic
#print axioms adapted_profile_parameters
#print axioms adapted_profile_admissible
#print axioms shellWeightSum_closed
#print axioms shellTaperMass_closed
#print axioms taperProfile_mass_closed
#print axioms taperProfile_degree_slack
end Paper5.PrecisionOpt
