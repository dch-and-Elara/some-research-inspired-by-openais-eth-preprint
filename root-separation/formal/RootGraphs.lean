import RootEntry

namespace RootSeparation

open GraphCutMoments

/-- Disjoint K4s exhibit unbounded admissible cubic sizes for the enumeration
argument, which needs no expansion. The paper's expanders are also covered. -/
def cliques (k : ℕ) : Finset ((Fin k × Fin 4) × (Fin k × Fin 4)) :=
  Finset.univ.filter fun e => e.1.1 = e.2.1 ∧ e.1.2 < e.2.2

theorem cliques_simple (k : ℕ) : Entry.Simple (cliques k) := by
  constructor
  · rintro ⟨u,v⟩ h hEq
    change u = v at hEq
    subst v
    simp [cliques] at h
  · rintro u v h₁ h₂
    simp [cliques] at h₁ h₂
    exact (not_lt_of_ge h₁.2.le) h₂.2

private theorem clique_fibers (k : ℕ) (g : Fin k) (v : Fin 4) :
    ((cliques k).filter (fun e => e.1 = (g,v))) =
      (Finset.univ.filter (fun w : Fin 4 => v < w)).map
        ⟨fun w => ((g,v),(g,w)), by intro x y h; exact congrArg (fun e => e.2.2) h⟩ ∧
    ((cliques k).filter (fun e => e.2 = (g,v))) =
      (Finset.univ.filter (fun w : Fin 4 => w < v)).map
        ⟨fun w => ((g,w),(g,v)), by intro x y h; exact congrArg (fun e => e.1.2) h⟩ := by
  constructor
  · ext e
    rcases e with ⟨⟨g₁,x⟩,⟨g₂,y⟩⟩
    simp only [cliques, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨rfl,h⟩,rfl,rfl⟩
      exact ⟨y,h,by simp⟩
    · rintro ⟨w,h,hw⟩
      obtain ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩ := hw
      exact ⟨⟨rfl,h⟩,rfl,rfl⟩
  · ext e
    rcases e with ⟨⟨g₁,x⟩,⟨g₂,y⟩⟩
    simp only [cliques, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨rfl,h⟩,rfl,rfl⟩
      exact ⟨x,h,by simp⟩
    · rintro ⟨w,h,hw⟩
      obtain ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩ := hw
      exact ⟨⟨rfl,h⟩,rfl,rfl⟩

theorem cliques_cubic (k : ℕ) (x : Fin k × Fin 4) : degree (cliques k) x = 3 := by
  rcases x with ⟨g,v⟩
  obtain ⟨h₁,h₂⟩ := clique_fibers k g v
  rw [degree, h₁, h₂, Finset.card_map, Finset.card_map]
  fin_cases v <;> decide

theorem cliques_size (k : ℕ) : Fintype.card (Fin k × Fin 4) = 4*k := by simp [Nat.mul_comm]

#print axioms cliques_simple
#print axioms cliques_cubic
#print axioms cliques_size

end RootSeparation
