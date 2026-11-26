import P5LiteralA10

/-! The manuscript's Smith list belongs to the scalar observation
matrix. Repeating it N times for vector observations is proved, not
supplied as a stronger Smith premise. -/
namespace Paper5
open scoped BigOperators Polynomial

variable {R : Type*} [CommRing R] {T : Type*}

noncomputable def scalarObserve (π : R) (t α : T→R) (P k : T→ℕ) (s : ℕ) :
    (Fin s→R) →ₗ[R] (∀ u : T, LocalJet π (P u) (k u)) :=
  LinearMap.pi fun u =>
    (nativeObs π (t u) (α u) (P u) (k u)).toLinearMap.comp
      ((testVecLin (I:=Unit) s ()).comp (LinearMap.pi fun (j : Unit × Fin s) => LinearMap.proj j.2))

/-- Taking a column coordinate of observed vector data is the same
as running the scalar observer on that column's own input polynomial. -/
theorem scalarObserve_column {I : Type*} [Fintype I] (π : R) (t α : T→R)
    (P k : T→ℕ) (s : ℕ) (x : I × Fin s→R) (i : I) (u : T) :
    observeGrid π t α P k s x u i = scalarObserve π t α P k s (fun a => x (i,a)) u := rfl

noncomputable def vectorObservationEquiv {I : Type*} [Fintype I] (π : R)
    (t α : T→R) (P k : T→ℕ) (s : ℕ) :
    LinearMap.range (observeGrid (I:=I) π t α P k s) ≃ₗ[R]
      (I → LinearMap.range (scalarObserve π t α P k s)) where
  toFun y i := ⟨fun u => y.val u i,by
    obtain ⟨x,hx⟩ := y.property
    refine ⟨fun a => x (i,a),?_⟩
    funext u
    exact (scalarObserve_column π t α P k s x i u).symm.trans (congrFun (congrFun hx u) i)⟩
  invFun y := ⟨fun u i => (y i).val u,by
    classical
    choose x hx using fun i => (y i).property
    refine ⟨fun j => x j.1 j.2,?_⟩
    funext u i
    exact (scalarObserve_column π t α P k s (fun j => x j.1 j.2) i u).trans (congrFun (hx i) u)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def repeatScalarGrid (π : R) {N m d : ℕ} (lo : Fin m→ℕ) (hi : Fin d→ℕ) :
    (Fin N → CyclicGrid π (Sum.elim lo hi)) ≃ₗ[R]
      CyclicGrid π (repExponent lo hi : RepIndex N m d→ℕ) where
  toFun y i := match i with
    | .inl j => y j.1 (.inl j.2)
    | .inr j => y j.1 (.inr j.2)
  invFun y n i := match i with
    | .inl j => y (.inl (n,j))
    | .inr j => y (.inr (n,j))
  left_inv y := by funext n i; cases i <;> rfl
  right_inv y := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' a x := by funext i; cases i <;> rfl

variable [IsDomain R] [IsLocalRing R] [Fintype T]

theorem native_observation_length_scalarSmith {N m d : ℕ}
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k : T→ℕ) (hs : m+d = ∑ u,k u)
    (A : Matrix (Fin N) (Fin N) R[X])
    (hdegree : ∀ i j, (A i j).natDegree≤d)
    (hregular : (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det≠0)
    (lo : Fin m→ℕ) (hi : Fin d→ℕ) (hsep : ∀ a b,lo a≤hi b)
    (smith : LinearMap.range (scalarObserve π t α P k (∑ u,k u)) ≃ₗ[R]
      CyclicGrid π (Sum.elim lo hi)) :
    (N * ∑ a,lo a : ℕ) ≤
      ∑ u, Module.length R (LinearMap.range (localMul A π (t u) (α u) (P u) (k u))) :=
  native_observation_length π hπ hmax t α P k hs A hdegree hregular lo hi hsep
    ((vectorObservationEquiv (I:=Fin N) π t α P k (∑ u,k u)).trans
      ((LinearEquiv.piCongrRight fun _ => smith).trans (repeatScalarGrid π lo hi)))

#print axioms scalarObserve_column
#print axioms vectorObservationEquiv
#print axioms repeatScalarGrid
#print axioms native_observation_length_scalarSmith
end Paper5
