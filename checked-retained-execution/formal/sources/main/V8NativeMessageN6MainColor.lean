import V8NativeMessageN6MainTriangles

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

/-! Exact finite averaging over all Boolean group colorings. This
contains no random input or certificate supplied by a caller. -/
namespace V8NativeMessage.N6
open scoped Classical BigOperators
noncomputable section

variable {G T : Type*} [Fintype G] [DecidableEq G] [Fintype T]

def flipColor (g : G) : Equiv.Perm (G→Bool) where
  toFun c x := if x=g then !(c x) else c x
  invFun c x := if x=g then !(c x) else c x
  left_inv c := by funext x; by_cases h : x=g <;> simp [h]
  right_inv c := by funext x; by_cases h : x=g <;> simp [h]

def cutBit (u v : G) (χ : G→Bool) : ℕ := if χ u≠χ v then 1 else 0

omit [Fintype G] in
theorem flip_crosses_complement (u v : G) (ne : u≠v) (χ : G→Bool) :
    cutBit u v χ + cutBit u v (flipColor u χ)=1 := by
  cases h₁ : χ u <;> cases h₂ : χ v <;> simp [cutBit,flipColor,ne.symm,h₁,h₂]

theorem cut_half (u v : G) (ne : u≠v) :
    2*(∑ χ : G→Bool, cutBit u v χ)=Fintype.card (G→Bool) := by
  have h : (∑ χ : G→Bool, (cutBit u v χ+cutBit u v (flipColor u χ))) =
      ∑ _χ : G→Bool, 1 := by
    apply Finset.sum_congr rfl
    exact fun χ _ => flip_crosses_complement u v ne χ
  rw [Finset.sum_add_distrib, Equiv.sum_comp (flipColor u) (cutBit u v)] at h
  simpa only [two_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using h

omit [Fintype G] [DecidableEq G] in
theorem cutCount_eq (a b : T→G) (χ : G→Bool) :
    (∑ v, cutBit (a v) (b v) χ) =
      Fintype.card {v : T // χ (a v)≠χ (b v)} := by
  simp only [cutBit,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]

/-- For any fixed distinct-color candidate pair at each site, there
is one common coloring crossing at least half of those pairs. -/
theorem half_cut (a b : T→G) (ne : ∀ i, a i≠b i) :
    ∃ χ : G→Bool, Fintype.card T ≤ 2*Fintype.card {i : T // χ (a i)≠χ (b i)} := by
  let count (χ : G→Bool) : ℕ := ∑ i, cutBit (a i) (b i) χ
  obtain ⟨χ,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (G→Bool))
    count ⟨fun _=>false,Finset.mem_univ _⟩
  have total :
      Fintype.card (G→Bool)*Fintype.card T=2*(∑ ψ : G→Bool, count ψ) := by
    calc
      _ = ∑ _i : T, Fintype.card (G→Bool) := by simp [Nat.mul_comm]
      _ = ∑ i : T, 2*(∑ ψ : G→Bool, cutBit (a i) (b i) ψ) := by
        apply Finset.sum_congr rfl
        exact fun i _ => (cut_half (a i) (b i) (ne i)).symm
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  have hb : (∑ ψ : G→Bool, count ψ)≤Fintype.card (G→Bool)*count χ := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      (Finset.sum_le_sum (fun ψ hψ => hmax ψ hψ) :
        (∑ ψ : G→Bool, count ψ)≤∑ _ψ : G→Bool, count χ)
  have hc : 0<Fintype.card (G→Bool) := Fintype.card_pos_iff.mpr ⟨fun _=>false⟩
  refine ⟨χ,?_⟩
  have h : Fintype.card (G→Bool)*Fintype.card T ≤
      Fintype.card (G→Bool)*(2*count χ) := by
    rw [total]
    simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left 2 hb
  have hnew := Nat.le_of_mul_le_mul_left h hc
  simpa only [count,cutCount_eq] using hnew

#print axioms flip_crosses_complement
#print axioms cut_half
#print axioms cutCount_eq
#print axioms half_cut

end
end V8NativeMessage.N6
