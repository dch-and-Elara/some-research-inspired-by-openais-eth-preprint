import P5MainBalanceM6BasisCell
import P5MainBalanceM6PrintedSchedule

/-! Exact one-axis sign distribution of the original common swap
eigenbasis: r diagonals and an involutive pairing of the other cells. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Real
open scoped BigOperators Classical

variable {B : Type*} [Fintype B] [LinearOrder B]

noncomputable def negativeAxis : Finset (B×B) :=
  Finset.univ.filter (fun p=>p.2<p.1)

noncomputable def positiveOffDiagonal : Finset (B×B) :=
  Finset.univ.filter (fun p=>p.1<p.2)

noncomputable def diagonalAxis : Finset (B×B) :=
  Finset.univ.filter (fun p=>p.1=p.2)

theorem opposite_axis_counts :
    (positiveOffDiagonal (B:=B)).card=(negativeAxis (B:=B)).card := by
  refine Finset.card_bij (fun p _=>p.swap) ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩
  · intro a _ b _ h
    exact Prod.swap_injective h
  · intro p hp
    exact ⟨p.swap,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩,Prod.swap_swap _⟩

theorem diagonal_axis_count : (diagonalAxis (B:=B)).card=Fintype.card B := by
  have he : (diagonalAxis (B:=B)) = Finset.univ.image (fun b : B=>(b,b)) := by
    ext p
    simp only [diagonalAxis,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    exact ⟨fun h=>⟨p.1,Prod.ext rfl h⟩,fun ⟨b,h⟩=>(congrArg Prod.fst h).symm.trans (congrArg Prod.snd h)⟩
  rw [he,Finset.card_image_of_injective _ (fun b c h=>congrArg Prod.fst h),Finset.card_univ]

theorem negative_axis_exact :
    2*(negativeAxis (B:=B)).card+Fintype.card B=(Fintype.card B)^2 := by
  have he : (positiveOffDiagonal (B:=B)∪negativeAxis)∪diagonalAxis=Finset.univ := by
    ext p
    simp only [positiveOffDiagonal,negativeAxis,diagonalAxis,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    rcases lt_trichotomy p.1 p.2 with h|h|h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have h1 : Disjoint (positiveOffDiagonal (B:=B)) negativeAxis := by
    rw [Finset.disjoint_left]
    intro p hp hn
    exact (not_lt_of_ge (Finset.mem_filter.mp hp).2.le) (Finset.mem_filter.mp hn).2
  have h2 : Disjoint (positiveOffDiagonal (B:=B)∪negativeAxis) diagonalAxis := by
    rw [Finset.disjoint_left]
    intro p hp heq
    have h := (Finset.mem_filter.mp heq).2
    rcases Finset.mem_union.mp hp with hp|hn
    · exact (Finset.mem_filter.mp hp).2.ne h
    · exact (Finset.mem_filter.mp hn).2.ne h.symm
  have hc := congrArg Finset.card he
  rw [Finset.card_union_of_disjoint h2,Finset.card_union_of_disjoint h1,
    opposite_axis_counts,diagonal_axis_count,Finset.card_univ,Fintype.card_prod] at hc
  simpa only [two_mul,pow_two] using hc

theorem negative_axis_probability [Nonempty B] :
    ((negativeAxis (B:=B)).card:ℝ)/(Fintype.card (B×B):ℝ) =
      ((Fintype.card B:ℝ)-1)/(2*(Fintype.card B:ℝ)) := by
  have hb : 0<(Fintype.card B:ℝ) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card B)
  have h := negative_axis_exact (B:=B)
  have h' : 2*((negativeAxis (B:=B)).card:ℝ)+(Fintype.card B:ℝ)=(Fintype.card B:ℝ)^2 := by exact_mod_cast h
  rw [Fintype.card_prod,Nat.cast_mul]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  nlinarith only [congrArg (fun x : ℝ=>(Fintype.card B:ℝ)*x) h']

#print axioms opposite_axis_counts
#print axioms diagonal_axis_count
#print axioms negative_axis_exact
#print axioms negative_axis_probability
end P5MainBalance.M6
