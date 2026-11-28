import V8CapacityMonicBasis

/-! A concrete linear extension of the coordinate order on the actual
finite total-degree grid. Equal-degree ties use any finite enumeration. -/
namespace V8CapacityGridOrder
open scoped Classical BigOperators
open V8CapacityMonicBasis

noncomputable section
set_option linter.unusedSectionVars false

variable {E : Type*} [Fintype E] {d : ℕ}

def score (x : Row E d) : ℕ := ∑ e : E, rowDegree x e

def code (x : Row E d) : ℕ :=
  score x * Fintype.card (Row E d)+(Fintype.equivFin _ x).val

theorem code_strict {x y : Row E d} (h : score x<score y) : code x<code y := by
  have hu := (Fintype.equivFin (Row E d) x).isLt
  have hstep := Nat.mul_le_mul_right (Fintype.card (Row E d)) (Nat.succ_le_of_lt h)
  unfold code
  rw [Nat.succ_mul] at hstep
  omega

theorem code_inj : Function.Injective (code (E:=E) (d:=d)) := by
  intro x y h
  have he : score x=score y :=
    le_antisymm (Nat.le_of_not_gt (fun hl => (code_strict hl).ne h.symm))
      (Nat.le_of_not_gt (fun hl => (code_strict hl).ne h))
  unfold code at h
  rw [he] at h
  exact (Fintype.equivFin _).injective (Fin.ext (Nat.add_left_cancel h))

def gridOrder : LinearOrder (Row E d) :=
  LinearOrder.lift' code code_inj

theorem coordinate_le {x y : Row E d} (h : ∀ e, rowDegree x e≤rowDegree y e) :
    @LE.le (Row E d) gridOrder.toLE x y := by
  change code x≤code y
  by_cases he : x=y
  · subst y
    exact le_rfl
  · have hn : ∃ e, rowDegree x e<rowDegree y e := by
      by_contra! nh
      apply he
      apply Subtype.ext
      funext e
      apply Fin.ext
      exact le_antisymm (h e) (nh e)
    obtain ⟨e,he⟩ := hn
    apply (code_strict (show score x<score y from ?_)).le
    unfold score
    exact Finset.sum_lt_sum (fun e _ => h e) ⟨e,Finset.mem_univ _,he⟩

#print axioms code_inj
#print axioms coordinate_le
end
end V8CapacityGridOrder

