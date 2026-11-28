
import J9R18CompiledCost
import J7PrintedParamsGraph

/-! The paper's four-clone sparse source has at most three bits per old
nonpin table. This fact comes from the actual incidence atlas, not from
an assumed small scope on the compiled readout. -/
namespace J9R18Compiled
open scoped Classical BigOperators
open J7PrintedParamsGraph J7ToJ8Incidence
noncomputable section
set_option linter.unusedSectionVars false

variable {Pair G : Type*} [Fintype Pair] [Fintype G]

theorem fourClone_port_count (ends : G×Bool≃J7SourceLabels.Pin Pair×Fin 3)
    (v : J7SourceLabels.OrdinaryColumn Pair (OldNonPrivate Pair G)) :
    Nat.card (Ports (column ends cycle) v) ≤ 3 := by
  classical
  cases v with
  | inl p =>
    rw [Nat.card_congr (clonePorts (column ends cycle) p),Nat.card_sum,Nat.card_unique,
      Nat.card_eq_fintype_card,Fintype.card_subtype]
    have h := clone_degree ends cycle p
    omega
  | inr c =>
    rw [Nat.card_congr (ordinaryPorts (column ends cycle) c), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    exact ordinary_degree ends cycle c

theorem fourClone_old_column_count (ends : G×Bool≃J7SourceLabels.Pin Pair×Fin 3) :
    Fintype.card (J7SourceLabels.OrdinaryColumn Pair (OldNonPrivate Pair G)) ≤
      Fintype.card (J7SourceLabels.Wire Pair (OrdinaryWire Pair G)) := by
  have h := Fintype.card_congr ends
  have hm := (actual_incidence ends).1
  simp only [J7SourceLabels.OrdinaryColumn, OldNonPrivate, Binary, Index,
    Fintype.card_prod,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin,Fintype.card_option]
    at h ⊢
  omega

theorem fourClone_compiledVisits_bound
    {Packet R : Type*} {L : ℕ} [Fintype Packet] [Fintype R]
    (ends : G×Bool≃J7SourceLabels.Pin Pair×Fin 3)
    (d : J8Physical.Layout Packet R (J7SourceLabels.Pin Pair)
      (J7SourceLabels.OrdinaryColumn Pair (OldNonPrivate Pair G))
      (Fin 64) (Ports (column ends cycle)) L) :
    let M := Fintype.card (J8Physical.Wire R)
    compiledVisits d ≤ 16 * Fintype.card (J7SourceLabels.Pin Pair) * (65+2*M)*M := by
  dsimp only
  have hWire := Fintype.card_congr (d.column.trans (colWire (column ends cycle)))
  have hOld := fourClone_old_column_count ends
  rw [← hWire] at hOld
  have hDegree (v : J7SourceLabels.OrdinaryColumn Pair (OldNonPrivate Pair G)) :
      Fintype.card (Ports (column ends cycle) v)≤3 := by
    rw [← Nat.card_eq_fintype_card]
    exact fourClone_port_count ends v
  refine (compiledVisits_bound d 3 hDegree).trans ?_
  rw [Fintype.card_fin]
  calc
    _ ≤ 2 * Fintype.card (J7SourceLabels.Pin Pair) *
      ((64 + 2 * Fintype.card (J8Physical.Wire R) + 1)*
        (Fintype.card (J8Physical.Wire R)*2^3)) := by
      gcongr
    _ = _ := by ring

#print axioms fourClone_port_count
#print axioms fourClone_old_column_count
#print axioms fourClone_compiledVisits_bound

end
end J9R18Compiled
