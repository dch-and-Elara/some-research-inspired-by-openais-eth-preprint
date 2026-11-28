import J6R11RepackRootChart
import J6R10RepackPrecision

/-! Link the planted/padded Boolean tensor network to the recursive
entry representation without assuming a root truth, a child response,
or a canonical lifting homomorphism. -/
namespace J6R11Repack
open scoped Classical BigOperators Polynomial
open J6OrientedHost J6R10Repack J6R9Recursive
variable {S V : Type*} [LinearOrder S] {a b m q l : ℕ}

theorem root_row_degree (T : Plant V m q) (w : Fin a → S)
    (v : Left V w m b l) :
    Nat.card {e : Wire w m b l // (rootNetwork T w).row e = v} =
      Nat.card (oldScope T w v) :=
  Nat.card_congr (chartFiber (rootRowChart T w) v).symm

theorem root_col_degree (T : Plant V m q) (w : Fin a → S)
    (v : Right w m b l q) :
    Nat.card {e : Wire w m b l // (rootNetwork T w).col e = v} = 2 := by
  exact (Nat.card_congr (chartFiber (rootColChart (b:=b) (l:=l) T w) v).symm).trans
    (by rw [Nat.card_eq_fintype_card,Fintype.card_bool])

theorem root_max_degree (T : Plant V m q) (w : Fin a → S) (Δ : ℕ)
    (hΔ : 2 ≤ Δ) (hT : ∀ v, T.degree v ≤ Δ) :
    (∀ v : Left V w m b l,
      Nat.card {e : Wire w m b l // (rootNetwork T w).row e = v} ≤ Δ) ∧
    (∀ v : Right w m b l q,
      Nat.card {e : Wire w m b l // (rootNetwork T w).col e = v} ≤ Δ) := by
  constructor
  · intro v
    rw [root_row_degree]
    rcases v with ⟨u,j⟩|⟨pad,sign⟩
    · simpa only [oldScope,Nat.card_fin] using hT u
    · have hh : Nat.card Unit = 1 := Nat.card_unique
      rw [oldScope,hh]
      omega
  · intro v
    rwa [root_col_degree]

def rootFlag (T : Plant V m q) (w : Fin a → S) (x : Wire w m b l → Bool) :
    Left V w m b l ⊕ Right w m b l q → Bool
  | .inl v => rowTable T w v (fun j => x (rowPort T w v j))
  | .inr v => colTable w v (fun j => x (colPort T w v j))

noncomputable def rootEntryFile (f : ℤ[X]) (ell p : ℕ) (T : Plant V m q) (w : Fin a → S) :
    EntryFile f ell (rootNetwork (b:=b) (l:=l) T w)
  | .inl v => ⟨p, fun y => if rowTable T w v
      (fun j => y ⟨.inl (rowPort T w v j),congrArg Sum.inl (root_row_owner T w v j)⟩) then 1 else 0⟩
  | .inr v => ⟨p, fun y => if colTable w v
      (fun j => y ⟨.inr (colPort T w v j),congrArg Sum.inr (root_col_owner T w v j)⟩) then 1 else 0⟩

theorem root_created (f : ℤ[X]) (ell p : ℕ) (T : Plant V m q) (w : Fin a → S)
    (v : Left V w m b l ⊕ Right w m b l q) :
    (rootEntryFile f ell p T w v).created = p := by cases v <;> rfl

theorem root_gate_read (f : ℤ[X]) (ell p : ℕ) (T : Plant V m q) (w : Fin a → S)
    (hf : f.Monic) (x : Wire w m b l → Bool) (v : Left V w m b l ⊕ Right w m b l q) :
    reduce p f ell ((rootEntryFile f ell p T w v).frozen hf (assignment (rootNetwork T w) x v)) =
      if rootFlag T w x v then 1 else 0 := by
  cases v with
  | inl v => exact (rootEntryFile f ell p T w (.inl v)).read_created hf _
  | inr v => exact (rootEntryFile f ell p T w (.inr v)).read_created hf _

/-- Independent input bits on the actual root edge chart, with the
original source Boolean tensors in the literal receiving ring. -/
theorem root_truth_at_creation [Fintype S] [Fintype V]
    (f : ℤ[X]) (ell p : ℕ) (T : Plant V m q) (w : Fin a → S)
    (hf : f.Monic) :
    reduce p f ell (trueContraction (rootNetwork (b:=b) (l:=l) T w)
      (rootEntryFile f ell p T w) hf) =
      ∑ x : Wire w m b l → Bool, ∏ v : Left V w m b l ⊕ Right w m b l q,
        if rootFlag T w x v then 1 else 0 := by
  classical
  unfold trueContraction
  rw [map_sum]
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun x _ => ?_)
  rw [map_prod]
  exact Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ]))
    (fun v _ => root_gate_read f ell p T w hf x v)

#print axioms root_row_degree
#print axioms root_col_degree
#print axioms root_max_degree
#print axioms root_created
#print axioms root_gate_read
#print axioms root_truth_at_creation
end J6R11Repack
