import P5HermiteTransportGenericExpansion
import PrecisionLattice

/-! H.2 before spelling the lattice test as valuations. Replacements
vary independently at each actual node, order, and matrix coordinate.
A difference of the actual transplanted matrices is proved to be the
original PrecisionLattice decoder on that coordinate. -/
namespace Paper5.HermiteGeneric
open Matrix PrecisionLattice
open scoped BigOperators Kronecker Classical

variable {R K T U V : Type*} [CommRing R] [Field K] [Algebra R K]
  [Fintype T] [DecidableEq T]

abbrev Slot (L : Layout K T) := Σ t : T,Fin (L.order t)

noncomputable def decoderTable (L : Layout K T) (b : ℕ) :
    (Fin b × Fin b)→Slot L→K :=
  fun ij s=>transfer L b s.1 s.2 ij.1 ij.2

def Permissible (L : Layout K T) (π : R) (P : Slot L→ℕ)
    (A B : (t : T)→Fin (L.order t)→Matrix U V K) : Prop :=
  ∀ t j u v,∃ e : R,B t j u v-A t j u v=algebraMap R K (π^(P ⟨t,j⟩)*e)

noncomputable def perturb (L : Layout K T) (π : R) (P : Slot L→ℕ)
    (A : (t : T)→Fin (L.order t)→Matrix U V K) (e : Slot L→U→V→R) :
    (t : T)→Fin (L.order t)→Matrix U V K :=
  fun t j=>Matrix.of (fun u v=>A t j u v+algebraMap R K (π^(P ⟨t,j⟩)*e ⟨t,j⟩ u v))

omit [Fintype T] [DecidableEq T] in
theorem permissible_iff_perturb (L : Layout K T) (π : R) (P : Slot L→ℕ)
    (A B : (t : T)→Fin (L.order t)→Matrix U V K) :
    Permissible L π P A B ↔ ∃ e : Slot L→U→V→R,B=perturb L π P A e := by
  constructor
  · intro h
    choose e he using fun (s : Slot L) u v=>h s.1 s.2 u v
    refine ⟨e,?_⟩
    funext t j
    apply Matrix.ext
    intro u v
    change B t j u v=A t j u v+algebraMap R K (π^(P ⟨t,j⟩)*e ⟨t,j⟩ u v)
    rw [add_comm]
    exact (sub_eq_iff_eq_add.mp (he ⟨t,j⟩ u v))
  · rintro ⟨e,rfl⟩ t j u v
    refine ⟨e ⟨t,j⟩ u v,?_⟩
    change A t j u v+algebraMap R K (π^(P ⟨t,j⟩)*e ⟨t,j⟩ u v)-A t j u v=_
    exact add_sub_cancel_left _ _

theorem perturbation_actual_entry (L : Layout K T) (b : ℕ) (π : R)
    (P : Slot L→ℕ) (A : (t : T)→Fin (L.order t)→Matrix U V K)
    (e : Slot L→U→V→R) (i j : Fin b) (u : U) (v : V) :
    expanded L b (perturb L π P A e) (i,u) (j,v)-expanded L b A (i,u) (j,v) =
      matrixError (decoderTable L b) (fun s=>π^(P s)) (fun s=>e s u v) (i,j) := by
  unfold expanded matrixError
  simp only [Matrix.sum_apply,Matrix.kronecker_apply]
  rw [←Finset.sum_sub_distrib,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j' _
  change transfer L b t j' i j * (A t j' u v+algebraMap R K (π^(P ⟨t,j'⟩)*e ⟨t,j'⟩ u v)) -
    transfer L b t j' i j * A t j' u v =
      transfer L b t j' i j * (algebraMap R K (π^(P ⟨t,j'⟩))*algebraMap R K (e ⟨t,j'⟩ u v))
  rw [map_mul,mul_add,add_sub_cancel_left]

def EntryPrecision {X Y : Type*} (π : R) (p : ℕ) (A B : Matrix X Y K) : Prop :=
  ∀ x y,∃ e : R, B x y-A x y=algebraMap R K (π^p*e)

variable [Nonempty U] [Nonempty V]

theorem independent_error_lattice_iff (L : Layout K T) (b : ℕ) (π : R)
    (P : Slot L→ℕ) (p : ℕ) (A : (t : T)→Fin (L.order t)→Matrix U V K) :
    (∀ B,Permissible L π P A B → EntryPrecision π p (expanded L b A) (expanded L b B)) ↔
      ∀ (i j : Fin b) (s : Slot L),∃ u : R,
       transfer L b s.1 s.2 i j * algebraMap R K (π^(P s)) = algebraMap R K (π^p*u) := by
  have h := matrix_power_precision_iff (decoderTable L b) π P (fun _=>p)
  constructor
  · intro H
    have hrows : ∀ (e : Slot L→R) (ij : Fin b × Fin b),∃ r : R,
      matrixError (decoderTable L b) (fun s=>π^(P s)) e ij=algebraMap R K (π^p*r) := by
      intro e ij
      let u : U := Classical.choice inferInstance
      let v : V := Classical.choice inferInstance
      let f : Slot L→U→V→R := fun s _ _=>e s
      have hp := H (perturb L π P A f)
        ((permissible_iff_perturb L π P A _).2 ⟨f,rfl⟩) (ij.1,u) (ij.2,v)
      rw [perturbation_actual_entry] at hp
      exact hp
    exact fun i j s=>(h.1 hrows) (i,j) s
  · intro H B hB
    obtain ⟨e,rfl⟩ := (permissible_iff_perturb L π P A B).1 hB
    rintro ⟨i,u⟩ ⟨j,v⟩
    rw [perturbation_actual_entry]
    exact h.2 (fun ij s=>H ij.1 ij.2 s) (fun s=>e s u v) (i,j)

#print axioms permissible_iff_perturb
#print axioms perturbation_actual_entry
#print axioms independent_error_lattice_iff
end Paper5.HermiteGeneric
