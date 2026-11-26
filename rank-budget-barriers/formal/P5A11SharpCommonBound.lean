import P5A11SharpCommonFinal

/-! Substitute the actual common-precision Hasse profile into the A.10
length lower bound, without asking for a second cyclic-list receipt. -/
namespace Paper5.CommonJets
open scoped BigOperators Polynomial Classical

variable {R T : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Fintype T] [LinearOrder T]

set_option maxHeartbeats 12000000 in
theorem a10_full_with_equal_precision_hasse_list {π : R} {t a : T→R} {k : T→ℕ}
    (D : IntegralHasseSmith π t a k) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (P : ℕ)
    {N m d : ℕ} (hs : m+d=∑u,k u)
    (A : Matrix (Fin N) (Fin N) R[X])
    (hdegree : ∀ i j,(A i j).natDegree≤d)
    (hregular : (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det≠0) :
    let hle : m≤∑u,k u := hs ▸ Nat.le_add_right m d
    ((N*∑ i : Fin m,clipped P (D.valuationList (Fin.castLE hle i).rev):ℕ):ENat) ≤
      ∑ u, Module.length R (LinearMap.range (localMul A π (t u) (a u) P (k u))) := by
  let e : Fin m ⊕ Fin d ≃ Fin (∑u,k u) := finSumFinEquiv.trans (finCongr hs)
  let q (i : Fin (∑u,k u)) := clipped P (D.valuationList i.rev)
  let lo (i : Fin m) := q (e (.inl i))
  let hi (i : Fin d) := q (e (.inr i))
  have hq : Monotone q := reversed_clipped_order P _ D.sorted
  have hsep (i : Fin m) (j : Fin d) : lo i≤hi j := by
    apply hq
    change i.val≤m+j.val
    have h := i.isLt
    omega
  obtain ⟨F⟩ := D.uniform_source_image hπ P
  have e' : CyclicGrid π q ≃ₗ[R] CyclicGrid π (q∘e) :=
    (LinearEquiv.piCongrLeft R (fun i=>Cyclic π (q i)) e).symm
  have he : q∘e=Sum.elim lo hi := by
    funext i
    cases i <;> rfl
  rw [he] at e'
  exact native_observation_length_scalarSmith π hπ hmax t a (fun _=>P) k
    hs A hdegree hregular lo hi hsep (F.trans e')

#print axioms a10_full_with_equal_precision_hasse_list
end Paper5.CommonJets
