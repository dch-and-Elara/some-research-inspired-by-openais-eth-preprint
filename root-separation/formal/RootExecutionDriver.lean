import RootExecution
import FourthPaperReview
import Mathlib.RingTheory.AdjoinRoot

namespace RootSeparation.Execution

open RootSeparation.Entry S11 GraphCutMoments Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V))
variable {R : ℤ → Type*} [∀ t, CommSemiring (R t)]
variable {I : Type*} [DecidableEq I]

abbrev Child := (t : ℤ) → ℕ → List ℕ → Fin 64 → R t
abbrev Codec := (t : ℤ) → R t ≃+ Coords I (nativePrecision E t)

noncomputable def executeProbe (reg : ∀ v, degree E v = 3)
    (hn : bigRoot (n (V := V))) (codec : Codec E (R := R) (I := I)) (track : I)
    (child : Child (R := R)) (t : ℤ) (j : ℕ) : BatchState I (nativePrecision E t) :=
  let G := chosenPacking E reg hn
  executeBatch (nativePrecision E t) (codec t) track (fun slot g => child t j slot.exponents g)
    (modeWeights (G.mixedAt t) (level t) (nativePrecision E t)) t j

theorem executeProbe_value (reg : ∀ v, degree E v = 3)
    (hn : bigRoot (n (V := V))) (codec : Codec E (R := R) (I := I)) (track : I)
    (child : Child (R := R)) (t : ℤ) (j : ℕ) :
    (codec t).symm (executeProbe E reg hn codec track child t j).accumulator =
      (sourceBatch (R := R) (chosenPacking E reg hn).mixedAt (rootM E) (rootL E) (rootA E)
        (rootU E) (initialPrecision (V := V)) child t j).1 := by
  let G := chosenPacking E reg hn
  let p := nativePrecision E t
  let eval := fun b : Slot => fun g : Fin 64 => child t j b.exponents g
  have h₁ := executeBatch_value p (codec t) track eval
    (modeWeights (G.mixedAt t) (level t) p) t j
  have h₂ := congrArg Prod.fst (sourceBatch_eq (R := R) G.mixedAt (rootM E)
    (rootL E) (rootA E) (rootU E) (initialPrecision (V := V)) child t j)
  have h₃ := runBatch_value (R := R t) (List.finRange 64) eval (batch (G.mixedAt t) t j p)
  unfold executeProbe
  rw [h₁, h₂, h₃]
  simp [batch, List.map_map, Function.comp_def]

omit [DecidableEq V] in
theorem nativePrecision_positive (t : ℤ) : 0 < nativePrecision E t := by
  change 0 < _ + _ + _
  unfold initialPrecision
  omega

theorem executeProbe_project (reg : ∀ v, degree E v = 3)
    (hn : bigRoot (n (V := V))) (codec : Codec E (R := R) (I := I)) (track : I)
    (child : Child (R := R)) (t : ℤ) (j : ℕ) :
    rootProjection (executeProbe E reg hn codec track child t j).trace =
      batch ((chosenPacking E reg hn).mixedAt t) t j (nativePrecision E t) := by
  unfold executeProbe batch
  exact executeBatch_project _ _ _ _ _ _ _ (nativePrecision_positive E t)

private theorem projection_flatMap {A : Type*} (l : List A) (f : A → List Step) :
    rootProjection (l.flatMap f) = l.flatMap (fun x => rootProjection (f x)) := by
  simp [rootProjection, executedDigits, List.filterMap_flatMap]

/-- TeX root loop with the sparse (subsumption-free) dispatcher.
The ghost trace is obtained from state-changing batch executions. -/
noncomputable def executeRoot (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (codec : Codec E (R := R) (I := I)) (track : I) (child : Child (R := R)) : List Step := by
  classical
  exact if hn : bigRoot (n (V := V)) then
    if dispatch (simpleNormalize (PinnedCNF.formula E σ)) = .sparse ∧ K < size E ∧
        leafThreshold (size E) < rootM E then
      (centers (rootU E) (rootL E)).toList.flatMap fun t =>
        (List.range (probeCount (rootM E) (rootL E))).flatMap fun j =>
          (executeProbe E reg hn codec track child t j).trace
    else []
  else []

/-- This comparison is positional and independent of the callback used in
the reference runEvents. The operands still determine the executed states. -/
theorem executeRoot_project {O : Type*} [CommRing O]
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (codec : Codec E (R := R) (I := I)) (track : I) (child : Child (R := R))
    (reference : NativeChild E O) :
    rootProjection (executeRoot E reg σ K codec track child) =
      runEvents E reg σ K reference := by
  classical
  by_cases hn : bigRoot (n (V := V))
  · rw [executeRoot, runEvents, dif_pos hn, dif_pos hn]
    split
    · rw [sourceTrace_eq_slots, rootSlots, projection_flatMap]
      congr 1
      funext t
      rw [projection_flatMap]
      congr 1
      funext j
      exact executeProbe_project E reg hn codec track child t j
    · rfl
  · rw [executeRoot, runEvents, dif_neg hn, dif_neg hn]
    rfl

theorem executeRoot_inject {O : Type*} [CommRing O]
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (codec : Codec E (R := R) (I := I)) (track : I) (child : Child (R := R))
    (reference : NativeChild E O) :
    let digs := executedDigits (executeRoot E reg σ K codec track child)
    let events := runEvents E reg σ K reference
    ∃ pos : Fin events.length → Fin digs.length, StrictMono pos ∧
      ∀ i, (digs.get (pos i)).firstSlot = some (events.get i) := by
  rw [← executeRoot_project E reg σ K codec track child reference]
  exact projection_ordered_injection _

/-- Only actual digit transitions in the tracked coordinate are charged. -/
noncomputable def executedRootWork (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (codec : Codec E (R := R) (I := I)) (track : I) (child : Child (R := R)) : ℕ :=
  (executedDigits (executeRoot E reg σ K codec track child)).length

theorem executed_root_lower (simple : Simple E) (reg : ∀ v, degree E v = 3)
    (σ : V → Bool) (K : ℕ) (codec : Codec E (R := R) (I := I))
    (track : I) (child : Child (R := R)) (hn : max (2^131071) K < n (V := V)) :
    (2 : ℝ)^((n (V := V) : ℝ) / (2*Real.sqrt (Real.logb 2 (n (V := V))))) ≤
      (executedRootWork E reg σ K codec track child : ℝ) := by
  let reference : NativeChild E ℤ := fun _ _ _ _ => 0
  have h := FourthPaperReview.exponential_root_visits E reg simple σ K reference hn
  rw [← executeRoot_project E reg σ K codec track child reference] at h
  exact h.trans (by
    exact_mod_cast (List.length_filterMap_le (f := Digit.firstSlot)
      (l := executedDigits (executeRoot E reg σ K codec track child))))

/-- An explicit root coefficient algebra at each printed precision.
A monic integer f of degree e remains monic of degree e after reduction. -/
abbrev residueRing (f : ℤ[X]) (p : ℕ) :=
  AdjoinRoot (f.map (Int.castRingHom (ZMod (2^p))))

noncomputable def polynomialCodec (f : ℤ[X]) (hf : f.Monic) {e : ℕ}
    (he : f.natDegree = e) (p : ℕ) (hp : 0 < p) : residueRing f p ≃+ Coords (Fin e) p := by
  haveI : Fact (1 < 2^p) := ⟨Nat.one_lt_two_pow (by omega)⟩
  let g := f.map (Int.castRingHom (ZMod (2^p)))
  have hg : g.Monic := hf.map _
  have hd : g.natDegree = e := (hf.natDegree_map _).trans he
  let reindex : (Fin g.natDegree → ZMod (2^p)) ≃+ Coords (Fin e) p :=
    { toFun := fun x i => x (Fin.cast hd.symm i)
      invFun := fun x i => x (Fin.cast hd i)
      left_inv := fun x => funext fun i => by simp
      right_inv := fun x => funext fun i => by simp
      map_add' := fun _ _ => rfl }
  exact (AdjoinRoot.powerBasisAux' hg).equivFun.toAddEquiv.trans reindex

noncomputable def trackedPolynomialWork (reg : ∀ v, degree E v = 3) (σ : V → Bool)
    (K : ℕ) (f : ℤ[X]) (hf : f.Monic) (he : f.natDegree = 4*lambda (size E))
    (positive : 0 < 4*lambda (size E)) (child : Child (R := fun t => residueRing f (nativePrecision E t))) : ℕ :=
  executedRootWork E reg σ K (fun t => polynomialCodec f hf he (nativePrecision E t) (nativePrecision_positive E t))
    ⟨0,positive⟩ child

theorem polynomial_root_lower (simple : Simple E) (reg : ∀ v, degree E v = 3) (σ : V → Bool)
    (K : ℕ) (f : ℤ[X]) (hf : f.Monic) (he : f.natDegree = 4*lambda (size E))
    (positive : 0 < 4*lambda (size E)) (child : Child (R := fun t => residueRing f (nativePrecision E t)))
    (hn : max (2^131071) K < n (V := V)) :
    (2 : ℝ)^((n (V := V) : ℝ) / (2*Real.sqrt (Real.logb 2 (n (V := V))))) ≤
      (trackedPolynomialWork E reg σ K f hf he positive child : ℝ) :=
  executed_root_lower E simple reg σ K _ _ child hn

#print axioms executeProbe_value
#print axioms executeRoot_project
#print axioms executeRoot_inject
#print axioms executed_root_lower
#print axioms polynomialCodec
#print axioms polynomial_root_lower
#check @executeRoot_inject
#check @polynomial_root_lower

end RootSeparation.Execution
