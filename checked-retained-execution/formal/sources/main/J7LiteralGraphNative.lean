import J7LiteralGraph

/-! # Actual simple edges and the native literal four-clone graph interface -/
open scoped BigOperators Classical

namespace J7LiteralGraph
open J7SourceLabels J7PrintedParams J7PrintedParamsGraph
open J7FullWordCells J7SeatSource J7SeatPacking J7SeatRounded P11FullPacking
open J7ToJ8Incidence J7ToJ8Layout J7ToJ8Canonical

noncomputable section
set_option maxHeartbeats 1500000

variable {V : Type*} [LinearOrder V] (H : SimpleGraph V) [Fintype V] [DecidableRel H.Adj]
variable (cubic : Cubic H)

theorem owner_inside (q : V × Fin 3) (b : Bool) :
    (pinToTriangle H cubic (endPin H cubic (.inr q) b)).1 = q.1 := by
  rw [inside_owners]
  cases b <;> rfl

/-- None of the indexed edges represent the same unordered endpoint pair.
Thus the replacement is a simple graph, not a multigraph shorthand. -/
theorem unique_unordered_edge (e f : TEdge H)
    (h : (∀ b, endPin H cubic e b = endPin H cubic f b) ∨
        (∀ b, endPin H cubic e b = endPin H cubic f (!b))) : e = f := by
  let owner := fun p : Pin (Edge H) => (pinToTriangle H cubic p).1
  have hOutIn (a : Edge H) (q : V × Fin 3) (map : Bool → Bool)
      (zz : ∀ b, endPin H cubic (.inl a) b = endPin H cubic (.inr q) (map b)) : False := by
    have l := congrArg owner (zz false)
    have r := congrArg owner (zz true)
    change (pinToTriangle H cubic (endPin H cubic (.inl a) false)).1 =
      (pinToTriangle H cubic (endPin H cubic (.inr q) (map false))).1 at l
    change (pinToTriangle H cubic (endPin H cubic (.inl a) true)).1 =
      (pinToTriangle H cubic (endPin H cubic (.inr q) (map true))).1 at r
    rw [(outside_owners H cubic a).1,owner_inside H cubic] at l
    rw [(outside_owners H cubic a).2,owner_inside H cubic] at r
    exact (ne_of_lt a.prop.1) (l.trans r.symm)
  rcases e with e | e <;> rcases f with f | f
  · rcases h with h | h
    · exact congrArg Sum.inl (congrArg Prod.fst (h false))
    · exact congrArg Sum.inl (congrArg Prod.fst (h false))
  · rcases h with h | h
    · exact (hOutIn e f id h).elim
    · exact (hOutIn e f not h).elim
  · rcases h with h | h
    · exact (hOutIn f e id (fun b => (h b).symm)).elim
    · exact (hOutIn f e not (fun b => by cases b; exact (h true).symm; exact (h false).symm)).elim
  · rcases h with h | h
    · have hh := congrArg (pinToTriangle H cubic) (h false)
      rw [inside_owners,inside_owners] at hh
      exact congrArg Sum.inr hh
    · have l := congrArg (pinToTriangle H cubic) (h false)
      have r := congrArg (pinToTriangle H cubic) (h true)
      rw [inside_owners,inside_owners] at l r
      have l' : e.2 = rot f.2 := congrArg Prod.snd l
      have r' : rot e.2 = f.2 := congrArg Prod.snd r
      have hh : ∀ j : Fin 3, rot (rot j) ≠ j := by decide
      exact (hh e.2 (by rw [r']; exact l'.symm)).elim

def literalGraph : SimpleGraph (Pin (Edge H)) where
  Adj x y := ∃ e : TEdge H,
    (endPin H cubic e false = x ∧ endPin H cubic e true = y) ∨
    (endPin H cubic e false = y ∧ endPin H cubic e true = x)
  symm := by
    intro x y h
    obtain ⟨e,h⟩ := h
    exact ⟨e,h.symm⟩
  loopless := by
    intro x h
    obtain ⟨e,h | h⟩ := h
    all_goals exact each_edge_has_two_distinct_ends H cubic e (h.1.trans h.2.symm)

include cubic in
theorem triangle_vertex_count : Fintype.card (Pin (Edge H)) = 3*Fintype.card V := by
  calc
    _ = Fintype.card (V × Fin 3) := Fintype.card_congr (pinToTriangle H cubic)
    _ = _ := by simp [Nat.mul_comm]

variable {A : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]

/-- The J7/J8 printed root for genuine ordered triangle replacement.
No incidence atlas is supplied: it is computed by sorting the actual
base graph's local neighbors and choosing the fixed triangle cycle. -/
theorem native_of_cubic (hA : Fintype.card A = 64)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin (Edge H)))) :
    let N := Fintype.card (Pin (Edge H))
    let t := rootT (sourceSize N)
    let col := column (atlas H cubic) cycle
    leafThreshold (sourceSize N) < 24*N ∧
    ∃ z : State A (Fin t → A) (Edge H) (OrdinaryRow (Edge H) (TEdge H)) (OldNonPrivate (Edge H) (TEdge H)),
      let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel Prod.fst col z))
      Nat.card (Page (t+1) b' A)*printedL t ≤ 3*(24*N) ∧
      ∃ j : Wire (Edge H) (OrdinaryWire (Edge H) (TEdge H)) ↪ Physical (t+1) b' A,
      ∃ preserve : ∀ w, physicalCell (balancedMask (t+1) b') (j w) = wordLabel Prod.fst col z w,
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      let d := physicalLayout Prod.fst col ordinary_row_exact_two z j preserve
      Nonempty (J8Physical.EndpointSeating d) ∧
      (∀ p (x : J8Physical.Wire (Subdivision (Edge H) (OrdinaryRow (Edge H) (TEdge H)))),
        ¬ J8Physical.Shift d x (J8Physical.pinWire d p)) ∧
      (∀ x y, J8Physical.Shift d x y → d.rowLabel x.1 = J8Physical.actualColLabel d y) ∧
      (∀ p, (J8Physical.targets d (J8Physical.pinWire d p)).Nonempty) :=
  literal_four_clone_native_root hA (atlas H cubic) large

#print axioms unique_unordered_edge
#print axioms literalGraph
#print axioms triangle_vertex_count
#print axioms native_of_cubic

end
end J7LiteralGraph
