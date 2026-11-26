
import S11GridValuation

noncomputable section
namespace S11
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def shellSet (a i : ℕ) : Finset ℤ :=
  ((grid (2^a)).erase 0).filter (fun z => level z = i)

theorem shell_card_lt {a i : ℕ} (hi : i < a) :
    (shellSet a i).card = 2^(a-i) := by
  classical
  let f := S7.gridNode i (a-i)
  have h : (Finset.univ : Finset (S7.Shell (a-i))).image f = shellSet a i := by
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and,shellSet,Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro ⟨q,rfl⟩
      have hv := S7.gridNode_valuation i (a-i) (by omega) q
      have hn : f q ≠ 0 := by
        unfold f S7.gridNode
        apply mul_ne_zero (by positivity)
        intro he
        exact S7.gridNode_oddPart (a-i) (by omega) q (he ▸ dvd_zero _)
      have hb := S7.gridNode_bounds i (a-i) q
      rw [show i+(a-i)=a by omega] at hb
      exact ⟨⟨hn,grid_bounds.2 hb⟩, hv⟩
    · rintro ⟨⟨hn,hm⟩,hi'⟩
      obtain ⟨hl,hh⟩ := grid_bounds.1 hm
      rw [← show i+(a-i)=a by omega] at hl hh
      exact S7.gridNode_exists i (a-i) (by omega) hl hh hn hi'
  rw [← h, Finset.card_image_of_injective _ (S7.gridNode_injective _ _), Finset.card_univ]
  exact Fintype.card_fin _

theorem shell_card_last (a : ℕ) : (shellSet a a).card = 1 := by
  have he : shellSet a a = {-(2:ℤ)^a} := by
    ext q
    simp only [shellSet,Finset.mem_filter,Finset.mem_erase,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hn,hq⟩,hv⟩
      have hd := padicValInt_dvd (p:=2) q
      rw [show padicValInt 2 q = a from hv] at hd
      obtain ⟨c,hc⟩ := hd
      have hg := grid_bounds.1 hq
      have hp : (0:ℤ)<2^a := by positivity
      rw [hc] at hg
      have hlo : -1 ≤ c := by
        apply le_of_mul_le_mul_left _ hp
        simpa using hg.1
      have hhi : c < 1 := by
        apply lt_of_mul_lt_mul_left _ hp.le
        simpa using hg.2
      have hnon : c ≠ 0 := by intro hz; apply hn; simp [hc,hz]
      rw [hc,show c = -1 by omega,mul_neg_one]
      push_cast
      rfl
    · rintro rfl
      have hp : (0:ℤ)<2^a := by positivity
      refine ⟨⟨by omega,grid_bounds.2 ⟨le_rfl,by omega⟩⟩,?_⟩
      exact (S7.v2_neg _).trans (S7.padicValInt_two_pow a)
  simp [he]

theorem shell_card {a i : ℕ} (hi : i ≤ a) : (shellSet a i).card = 2^(a-i) := by
  rcases hi.eq_or_lt with rfl|h
  · simp [shell_card_last]
  · exact shell_card_lt h

theorem shell_sum (a : ℕ) (f : ℕ → ℚ) :
    (∑ q ∈ (grid (2^a)).erase 0, f (level q)) =
      ∑ i ∈ Finset.range (a+1), (2:ℚ)^(a-i) * f i := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (grid (2^a)).erase 0) (t := Finset.range (a+1)) (g := level)
    (fun q hq => Finset.mem_range.2 (Nat.lt_succ_of_le
      (level_grid (Finset.mem_erase.1 hq).2 (Finset.mem_erase.1 hq).1))) (fun q => f (level q))]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ a := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
  change (∑ q ∈ shellSet a i, f (level q)) = _
  calc
    _ = ∑ _ ∈ shellSet a i, f i := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.1 hq).2]
    _ = _ := by simp [shell_card hi']

theorem excess_second_moment {a i : ℕ} (hi : i ≤ a) :
    (∑ q ∈ (grid (2^a)).erase 0, ((level q - i : ℕ):ℚ)^2) ≤ 6 * (2:ℚ)^(a-i) := by
  rw [shell_sum a (fun j => ((j-i:ℕ):ℚ)^2)]
  let f (j : ℕ) : ℚ := 2^(a-j) * ((j-i:ℕ):ℚ)^2
  change (∑ j ∈ Finset.range (a+1), f j) ≤ _
  rw [show a+1 = i+(a-i+1) by omega,Finset.sum_range_add]
  have hzero : (∑ j ∈ Finset.range i, f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [f,Nat.sub_eq_zero_of_le (Finset.mem_range.1 hj).le]
  rw [hzero, zero_add]
  have he : (∑ j ∈ Finset.range (a-i+1), f (i+j)) =
      (2:ℚ)^(a-i) * ∑ j ∈ Finset.range (a-i+1), (j:ℚ)^2 / 2^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i+j ≤ a := by have := Finset.mem_range.1 hj; omega
    unfold f
    rw [Nat.add_sub_cancel_left]
    have hh : (2:ℚ)^(a-i) = 2^(a-(i+j)) * 2^j := by rw [← pow_add]; congr 1; omega
    rw [hh]
    field_simp
  rw [he,S7.secondMoment]
  have hp : 0 ≤ ((↑(a-i):ℚ)^2+4*(a-i:ℕ)+6)/2^(a-i) := by positivity
  nlinarith only [mul_nonneg (by positivity : (0:ℚ)≤2^(a-i)) hp]

#print axioms shell_card
#print axioms shell_sum
#print axioms excess_second_moment

end S11

