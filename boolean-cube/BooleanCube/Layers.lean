import BooleanCube.Reduction
import Mathlib.LinearAlgebra.Lagrange

namespace LocalReconstruction
open Polynomial
open scoped Polynomial
noncomputable section

def ones {q : ℕ} (s : Cube q) : Finset (Fin q) := Finset.univ.filter fun i => s i = true
def weight {q : ℕ} (s : Cube q) : ℕ := (ones s).card
def layerFamily (q : ℕ) (K : Finset ℕ) : Set (Cube q) := {s | weight s ∈ K}

def gapsAtMost (q d : ℕ) (K : Finset ℕ) : Prop :=
  ∀ L U : ℕ, L ≤ U → U ≤ q → (∀ j, L ≤ j → j ≤ U → j ∉ K) → U-L ≤ d

private def inFace {q : ℕ} (F G : Finset (Fin q)) (s : Cube q) : Prop :=
  (∀ j ∈ F, s j = true) ∧ (∀ j : Fin q, j ∉ G → s j = false)

private theorem face_weights {q : ℕ} {F G : Finset (Fin q)} {s : Cube q} (hs : inFace F G s) :
    F.card ≤ weight s ∧ weight s ≤ G.card := by
  constructor
  · apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1 j hj⟩
  · apply Finset.card_le_card
    intro j hj
    by_contra a
    have h := (Finset.mem_filter.mp hj).2
    simp [hs.2 j a] at h

private theorem flip_off {q : ℕ} {i j : Fin q} (h : j ≠ i) (s : Cube q) :
    flip i s j = s j := by simp [flip, toggle, oneBit, h]

private theorem face_flip {q : ℕ} {F G : Finset (Fin q)} {i : Fin q}
    (hi : i ∈ G \ F) (s : Cube q) : inFace F G s ↔ inFace F G (flip i s) := by
  have go (a : Cube q) (ha : inFace F G a) : inFace F G (flip i a) := by
    constructor
    · intro j hj
      have hji : j ≠ i := by rintro rfl; exact (Finset.mem_sdiff.mp hi).2 hj
      rw [flip_off hji]
      exact ha.1 _ hj
    · intro j hj
      have hji : j ≠ i := by rintro rfl; exact hj (Finset.mem_sdiff.mp hi).1
      rw [flip_off hji]
      exact ha.2 _ hj
  exact ⟨go s, fun h => (flipEquiv i).left_inv s ▸ go (flip i s) h⟩

theorem layer_gap_lower {q d : ℕ} {labels : Fin q → ℚ} (hinj : Function.Injective labels)
    {K : Finset ℕ} {p : Cube q → ℚ[X]} (hp : edgeCondition labels (layerFamily q K) d p) :
    gapsAtMost q d K := by
  classical
  intro L U hLU hU miss
  obtain ⟨G,_,hG⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin q)))
    (n := U) (by simpa using hU)
  obtain ⟨F,hFG,hF⟩ := Finset.exists_subset_card_eq (s := G) (n := L) (hG ▸ hLU)
  let I := fun s : Cube q => inFace F G s
  let H : ℚ[X] := ∑ s : Cube q, if I s then p s else 0
  have bound : H.natDegree ≤ d := by
    apply natDegree_sum_le_of_forall_le
    intro s _
    split <;> simp_all [hp.1]
  have hn : H ≠ 0 := by
    have hm : inFace F G (fun j => decide (j ∈ F)) := by
      constructor
      · intro j hj; simp [hj]
      · intro j hj; simp [show j ∉ F from fun h => hj (hFG h)]
    have hpos : 0 < (Finset.univ.filter I).card :=
      Finset.card_pos.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩⟩
    intro h
    have e := congrArg (Polynomial.eval (0:ℚ)) h
    simp only [H, eval_finset_sum, apply_ite, hp.2.1, eval_zero, Finset.sum_boole] at e
    exact (Nat.ne_of_gt hpos) (by exact_mod_cast e)
  have retained {s : Cube q} (hs : I s) : s ∉ layerFamily q K := by
    have hw := face_weights hs
    exact miss _ (hF ▸ hw.1) (hG ▸ hw.2)
  have root (i : ↥(G \ F)) : H.eval (labels i) = 0 := by
    let v := fun s : Cube q => if I s then (p s).eval (labels i) else 0
    have hz (s : Cube q) : v s + v (flip i s) = 0 := by
      by_cases a : I s
      · have b : I (flip (i : Fin q) s) := (face_flip i.property s).mp a
        simpa only [v, if_pos a, if_pos b] using hp.2.2 i s (retained a) (retained b)
      · have b : ¬ I (flip i s) := fun h => a ((face_flip i.property s).mpr h)
        simp [v,a,b]
    have he : (∑ s, v (flip i s)) = ∑ s, v s := (flipEquiv (i : Fin q)).sum_comp v
    have hsum : (∑ s, v s) + (∑ s, v (flip i s)) = 0 := by
      rw [← Finset.sum_add_distrib]
      simp [hz]
    rw [he] at hsum
    have ez : ∑ s, v s = 0 := by linarith
    simpa only [H, eval_finset_sum, apply_ite, eval_zero, v] using ez
  by_contra! bad
  apply hn
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero H (hinj.comp Subtype.val_injective) root
  change H.natDegree < Fintype.card ↥(G \ F)
  rw [Fintype.card_coe, Finset.card_sdiff_of_subset hFG,hG,hF]
  exact bound.trans_lt bad

private def start (K : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => if n ∈ K then n+1 else start K n

private theorem start_le (K : Finset ℕ) (w : ℕ) : start K w ≤ w := by
  induction w with
  | zero => rfl
  | succ n ih => simp only [start]; split <;> omega

private theorem start_clear {K : Finset ℕ} {w : ℕ} (hw : w ∉ K) :
    ∀ j, start K w ≤ j → j ≤ w → j ∉ K := by
  induction w with
  | zero => intro j _ hj; have := Nat.eq_zero_of_le_zero hj; simpa [this] using hw
  | succ n ih =>
    intro j hlo hhi
    by_cases he : j = n+1
    · simpa [he] using hw
    · by_cases h : n ∈ K
      · simp [start,h] at hlo; omega
      · exact ih h j (by simpa [start,h] using hlo) (by omega)

private def parityPoly (L d : ℕ) : ℚ[X] :=
  Lagrange.interpolate (Finset.range (d+1)) (fun j : ℕ => ((L+j:ℕ):ℚ)) (fun j => (-1:ℚ)^(L+j))

private theorem nodes_inj (L : ℕ) : Function.Injective (fun j : ℕ => ((L+j:ℕ):ℚ)) := by
  intro a b h
  change ((L+a:ℕ):ℚ) = ((L+b:ℕ):ℚ) at h
  exact Nat.add_left_cancel (by exact_mod_cast h : L+a=L+b)

private theorem parity_degree (L d : ℕ) : (parityPoly L d).natDegree ≤ d := by
  apply natDegree_le_of_degree_le
  simpa [parityPoly] using Lagrange.degree_interpolate_le (s := Finset.range (d+1))
    (fun j => (-1:ℚ)^(L+j)) (nodes_inj L).injOn

private theorem parity_value {L d w : ℕ} (hL : L ≤ w) (hw : w-L ≤ d) :
    (parityPoly L d).eval (w:ℚ) = (-1:ℚ)^w := by
  have h := Lagrange.eval_interpolate_at_node (s := Finset.range (d+1))
    (fun j => (-1:ℚ)^(L+j)) (nodes_inj L).injOn
    (i := w-L) (Finset.mem_range.mpr (by omega))
  simpa [parityPoly, show L+(w-L)=w by omega] using h

private def nodePoly {q : ℕ} (a : Fin q → ℚ) (s : Cube q) : ℚ[X] :=
  ∑ i ∈ ones s, (1 - C (a i)⁻¹ * X)

private theorem node_degree {q : ℕ} (a : Fin q → ℚ) (s : Cube q) : (nodePoly a s).natDegree ≤ 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · simp
  · exact (natDegree_C_mul_le _ _).trans (by simp)

private theorem ones_flip {q : ℕ} {i : Fin q} {s : Cube q} (h : s i = false) :
    ones (flip i s) = insert i (ones s) := by
  ext j
  by_cases he : j = i
  · subst j; simp [ones, flip, toggle, oneBit,h]
  · simp [ones, flip_off he, he]

theorem layer_gap_upper {q d : ℕ} {a : Fin q → ℚ} (ha : ∀ i, a i ≠ 0)
    {K : Finset ℕ} (hg : gapsAtMost q d K) : ∃ p, edgeCondition a (layerFamily q K) d p := by
  classical
  let p := fun s : Cube q => if weight s ∈ K then 1 else
    C ((-1:ℚ)^(weight s)) * (parityPoly (start K (weight s)) d).comp (nodePoly a s)
  have forward (i : Fin q) (s : Cube q) (hb : s i = false)
      (hs : weight s ∉ K) (ht : weight (flip i s) ∉ K) :
      (p s).eval (a i) + (p (flip i s)).eval (a i) = 0 := by
    have hi : i ∉ ones s := by simp [ones,hb]
    have hw : weight (flip i s) = weight s + 1 := by
      simp [weight,ones_flip hb,hi]
    have ev : (nodePoly a (flip i s)).eval (a i) = (nodePoly a s).eval (a i) := by
      simp [nodePoly,ones_flip hb,hi,ha]
      ring
    simp only [p,if_neg hs,if_neg ht, eval_mul, eval_C, eval_comp, ev,hw, start, pow_succ]
    ring
  refine ⟨p,?_,?_,?_⟩
  · intro s
    dsimp [p]
    split
    · simp
    · exact (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans
        ((Nat.mul_le_mul (parity_degree _ _) (node_degree a s)).trans (by simp)))
  · intro s
    by_cases hs : weight s ∈ K
    · simp [p,hs]
    · have he : (nodePoly a s).eval 0 = (weight s:ℚ) := by
        simp [nodePoly,eval_finset_sum,weight]
      have wle : weight s ≤ q := by simpa [weight] using Finset.card_le_univ (ones s)
      have hb := hg _ _ (start_le K (weight s)) wle (start_clear hs)
      simp only [p,if_neg hs,eval_mul,eval_C,eval_comp,he,parity_value (start_le _ _) hb]
      rw [← mul_pow]
      norm_num
  · intro i s hs ht
    cases hb : s i with
    | false => exact forward i s hb hs ht
    | true =>
      have h2 : flip i (flip i s) = s := (flipEquiv i).left_inv s
      have h := forward i (flip i s) (by simp [flip,toggle,oneBit,hb]) ht (by rw [h2]; exact hs)
      rwa [h2,add_comm] at h

theorem layers_iff_gaps {q d : ℕ} {a : Fin q → ℚ} (hi : Function.Injective a)
    (hn : ∀ i, a i ≠ 0) (K : Finset ℕ) :
    (∃ p, edgeCondition a (layerFamily q K) d p) ↔ gapsAtMost q d K :=
  ⟨fun ⟨_,hp⟩ => layer_gap_lower hi hp, layer_gap_upper hn⟩

end
end LocalReconstruction
