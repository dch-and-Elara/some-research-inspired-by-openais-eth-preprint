import V8NativeMessageN4OrdinaryEnd

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3900000

/-! Original v8 N3 on the native four-copy MAIN register. The cut
partitions signed unary factors, not the private variable groups,
and is not specialized to an induced matching. -/
namespace V8NativeMessage.N3Literal
open scoped Classical BigOperators Polynomial
open V8NativeMessage.C3.NativeAssembly.MainScan
open Polynomial
noncomputable section

section Signs
variable {W : Type*}

abbrev RowWord (cut : W→Bool) := {v : W // cut v=true}→Bool
abbrev ColWord (cut : W→Bool) := {v : W // cut v=false}→Bool

def rows (cut : W→Bool) (x : RowWord cut) (v : W) : Bool :=
  if h : cut v=true then x ⟨v,h⟩ else true

def cols (cut : W→Bool) (y : ColWord cut) (v : W) : Bool :=
  if h : cut v=false then y ⟨v,h⟩ else true

def signs (cut : W→Bool) (x : RowWord cut) (y : ColWord cut) : W→Bool :=
  N6.splice cut (rows cut x) (cols cut y)

/-- No words on either side of the arbitrary sign cut are removed. -/
def cutCube (cut : W→Bool) : (RowWord cut × ColWord cut) ≃ (W→Bool) where
  toFun xy := signs cut xy.1 xy.2
  invFun σ := (fun v=>σ v.val,fun v=>σ v.val)
  left_inv := by
    intro xy
    apply Prod.ext
    · funext v
      simp [signs,N6.splice,rows,v.property]
    · funext v
      simp [signs,N6.splice,cols,v.property]
  right_inv := by
    intro σ
    funext v
    cases h : cut v <;> simp [signs,N6.splice,rows,cols,h]
end Signs

section Actual
variable {W : Type} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J) (reg : ∀v,GraphCutMoments.degree F v=3)
variable (h : feasible L.frame) (P : N6.FixedLists L)

abbrev Choices := ∀ g : Fin r, Fin (P.count g)

theorem expand_actual_choices (σ : W→Bool) :
    N6.completed L reg h P σ =
      ∑ u : Choices L P, ∏ g, N6.entry L reg h P g (u g) σ :=
  Fintype.prod_sum (fun g j => N6.entry L reg h P g j σ)

variable {k : ℕ} (fit : k≤J) (read : Jet k→ₗ[ℚ]ℚ) (cut : W→Bool)

def leftJet (u : Choices L P) (x : RowWord cut) : Jet k :=
  N4.shrink fit (∏ g, N6.leftPoint L reg h P g (u g) cut (rows cut x))

def rightJet (u : Choices L P) (y : ColWord cut) : Jet k :=
  N4.shrink fit (∏ g, N6.rightPoint L reg h P g (u g) cut (cols cut y))

theorem actual_choice_split (u : Choices L P) (x : RowWord cut) (y : ColWord cut) :
    N4.shrink fit (∏ g, N6.entry L reg h P g (u g) (signs cut x y)) =
      leftJet L reg h P fit cut u x * rightJet L reg h P fit cut u y := by
  unfold leftJet rightJet
  rw [← map_mul,← Finset.prod_mul_distrib]
  apply congrArg (N4.shrink fit)
  apply Finset.prod_congr rfl
  intro g _
  exact N6.point_factors L reg h P g (u g) cut (rows cut x) (cols cut y)

def sourceMatrix : Matrix (RowWord cut) (ColWord cut) ℚ :=
  Matrix.of fun x y => read (N4.shrink fit (N6.completed L reg h P (signs cut x y)))

def choiceMatrix (u : Choices L P) : Matrix (RowWord cut) (ColWord cut) ℚ :=
  N4.nativeMixed read (leftJet L reg h P fit cut u) (rightJet L reg h P fit cut u)
    (fun _=>1) (fun _=>1)

theorem original_N3_matrix_expansion :
    sourceMatrix L reg h P fit read cut = ∑ u, choiceMatrix L reg h P fit read cut u := by
  ext x y
  simp only [sourceMatrix,Matrix.of_apply,Matrix.sum_apply,choiceMatrix,N4.nativeMixed,mul_one]
  rw [expand_actual_choices L reg h P,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [actual_choice_split L reg h P fit cut u x y]

/-- The source keeps a single quotient jet of length k for each point
choice. No factor of k is paid separately for each MAIN group. -/
theorem original_N3_fixed_prefix :
    (sourceMatrix L reg h P fit read cut).rank ≤ k * ∏ g, P.count g := by
  rw [original_N3_matrix_expansion]
  apply (V8CapacityUnified.U7.rank_sum_le Finset.univ _).trans
  calc
    _ ≤ ∑ _ : Choices L P, k := by
      apply Finset.sum_le_sum
      intro u _
      simpa only [choiceMatrix,Fintype.card_fin] using
        N4.nativeMixed_rank (V8NativeMessage.C3.jetBasis ℚ k) read
          (leftJet L reg h P fit cut u) (rightJet L reg h P fit cut u)
          (fun _=>1) (fun _=>1)
    _ = _ := by simp [Choices,Fintype.card_pi,Nat.mul_comm]

theorem original_N3_fixed_full (readFull : Jet J→ₗ[ℚ]ℚ) :
    (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      readFull (N6.completed L reg h P (signs cut x y)))).rank≤ J*∏ g, P.count g := by
  simpa only [sourceMatrix,N4.shrink_self] using original_N3_fixed_prefix L reg h P (k:=J) le_rfl readFull cut

include h in
/-- Apply the same bound to the original completed exhaustive evaluator,
so every term in the actual eligible fiber is included. -/
theorem original_N3_scan_prefix :
    (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      read (N4.shrink fit ((nativeScan F reg L (signs cut x y)).2.2)))).rank≤
      k*∏ g, Fintype.card (N6.PrivateWord L g) := by
  have hh : (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      read (N4.shrink fit ((nativeScan F reg L (signs cut x y)).2.2)))) =
      sourceMatrix L reg h (N6.exhaustive L) fit read cut := by
    ext x y
    simp only [Matrix.of_apply,sourceMatrix,N6.exhaustive_completed L reg h]
  rw [hh]
  exact original_N3_fixed_prefix L reg h (N6.exhaustive L) fit read cut

include h in
theorem original_N3_scan_full (readFull : Jet J→ₗ[ℚ]ℚ) :
    (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      readFull ((nativeScan F reg L (signs cut x y)).2.2))).rank≤
      J*∏ g, Fintype.card (N6.PrivateWord L g) := by
  simpa only [N4.shrink_self] using original_N3_scan_prefix L reg h (k:=J) le_rfl readFull cut

#print axioms cutCube
#print axioms expand_actual_choices
#print axioms actual_choice_split
#print axioms original_N3_matrix_expansion
#print axioms original_N3_fixed_prefix
#print axioms original_N3_fixed_full
#print axioms original_N3_scan_prefix
#print axioms original_N3_scan_full

end Actual
end
end V8NativeMessage.N3Literal
