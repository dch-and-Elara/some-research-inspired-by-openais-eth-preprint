import J3R61Row

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4600000

/-! Integer first-jet factors for the *literal* MAIN clauses: positive
edge OR, implication-cycle (not equality), and selected signed unary. -/
namespace J3R61
open Polynomial V8NativeMessage
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open J3R38LiteralSingleton
open scoped BigOperators Polynomial Classical

def complement (D : ℤ) (r : Paid (Pair ℤ)) : Paid (Pair ℤ) :=
  ⟨(Pair.scalar D).minus r.value,r.ops+2⟩

def signedAt (D : ℤ) (r : Paid (Pair ℤ)) (s : Bool) : Paid (Pair ℤ) :=
  if s then r else complement D r

def binaryAt (D : ℤ) (a b : Paid (Pair ℤ)) : Paid (Pair ℤ) :=
  ⟨(Pair.scalar (D*D)).minus (a.value.times b.value),a.ops+b.ops+7⟩

def factorAt {W : Type*} {F : Finset (W×W)} (D : ℤ) (p : N1.Occ F → Paid (Pair ℤ))
    (s : W → Bool) : Clause F → Paid (Pair ℤ)
  | .inl v => signedAt D (p (.inl v)) (s v)
  | .inr (.inl e) => binaryAt D
      (complement D (p (.inr (.inl (e,true))))) (complement D (p (.inr (.inl (e,false)))))
  | .inr (.inr v) => binaryAt D
      (p (.inr (.inr (v,true)))) (complement D (p (.inr (.inr (v,false)))))

theorem factorAt_ops {W : Type*} {F : Finset (W×W)} (D : ℤ) (p : N1.Occ F → Paid (Pair ℤ))
    (s : W → Bool) (f : Clause F) (n : ℕ) (h : ∀ o, (p o).ops=n) :
    (factorAt D p s f).ops+4 ≤ (n+8)*N1.arity f := by
  rcases f with (v|e|j)
  · cases hv : s v <;> simp [factorAt,signedAt,complement,N1.arity,h,hv]
  · simp only [factorAt,binaryAt,complement,N1.arity,h]
    omega
  · simp only [factorAt,binaryAt,complement,N1.arity,h]
    omega

def paidProduct : List (Paid (Pair ℤ)) → Paid (Pair ℤ)
  | [] => ⟨Pair.scalar 1,0⟩
  | a :: as =>
    let b := paidProduct as
    ⟨a.value.times b.value,a.ops+b.ops+4⟩

theorem paidProduct_value (as : List (Paid (Pair ℤ))) :
    (paidProduct as).value = (product (as.map Paid.value)).value := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [paidProduct,List.map_cons,product,ih]

theorem paidProduct_ops {I : Type*} (f : I → Paid (Pair ℤ)) (w : I → ℕ) (l : List I)
    (h : ∀ i, (f i).ops+4 ≤ w i) :
    (paidProduct (l.map f)).ops ≤ (l.map w).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons,paidProduct,List.sum_cons]
    have hh := h i
    omega

theorem paidProduct_guarded_width {I : Type*} (f : I → Paid (Pair ℤ)) (deg : I → ℕ)
    (A : ℕ) (l : List I) (hf : ∀ i, (f i).value.intSize ≤ A^(deg i)) :
    (paidProduct (l.map f)).value.intSize ≤ A^((l.map deg).sum) := by
  induction l with
  | nil => simp [paidProduct,Pair.scalar,Pair.intSize]
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,paidProduct,pow_add]
    exact (pair_product_size _ _).trans (Nat.mul_le_mul (hf i) ih)

theorem intCapture_le_norm (p : ℤ[X]) : (capture p).intSize ≤ N1.coeffNorm p := by
  classical
  let s := p.support ∪ ({0,1} : Finset ℕ)
  have hn := N1.norm_over (p:=p) (s:=s) (Finset.subset_union_left)
  rw [hn]
  calc
    _ = ∑ j ∈ ({0,1} : Finset ℕ),(p.coeff j).natAbs := by
      simp [capture,Pair.intSize]
    _ ≤ _ := Finset.sum_le_sum_of_subset (fun j hj => Finset.mem_union_right _ hj)

theorem capture_C_square (D : ℤ) : capture (C D ^ 2) = Pair.scalar (D*D) := by
  rw [pow_two,capture_mul,capture_scalar]
  ext <;> simp [Pair.times,Pair.scalar]

@[simp] theorem capture_nat (D : ℕ) : capture (D:ℤ[X]) = Pair.scalar (D:ℤ) := by
  simpa only [Polynomial.C_eq_natCast] using (capture_scalar (D:ℤ))

@[simp] theorem capture_nat_square (D : ℕ) :
    capture ((D:ℤ[X])^2) = Pair.scalar ((D:ℤ)*(D:ℤ)) := by
  simpa only [Polynomial.C_eq_natCast] using capture_C_square (D:ℤ)

noncomputable section
variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

def literalRead (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (D R : ℕ) (i : Clone W) (o : N1.Occ F) : Paid (Pair ℤ) :=
  evalRow (coords W) (N1.row L hreg o) D R (N1.tInt L) i

theorem literalRead_at_printed (L : CloneTuple F r Q J)
    (hreg : ∀ v, GraphCutMoments.degree F v=3) (R : ℕ) (i : Clone W) (o : N1.Occ F) :
    literalRead L hreg (printedScale R Q).value R i o = literalRow L hreg R i o :=
  rfl

theorem literal_factor_same (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (i : Clone W) (hi : L.U={i}) (s : W → Bool) (f : Clause F) :
    (factorAt (N1.δ R Q : ℤ) (literalRead L hreg (N1.δ R Q) R i) s f).value =
      capture (N1.intFactor L hreg bounds s (fun _=>true) f) := by
  have hr (o : N1.Occ F) :
      (literalRead L hreg (N1.δ R Q) R i o).value =
        capture (N1.iTheta L hreg bounds (fun _=>true) o) := by
    rw [← (printedScale_exact R Q).1, literalRead_at_printed]
    exact literalRow_same_itheta L bounds i hi o
  rcases f with (v|e|j)
  · cases hv : s v <;>
      simp [factorAt,signedAt,complement,N1.intFactor,N1.intLiteral,hv,hr]
  · simp [factorAt,binaryAt,complement,N1.intFactor,N1.intLiteral,hr]
  · simp [factorAt,binaryAt,complement,N1.intFactor,N1.intLiteral,hr]

theorem literal_factor_width (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (i : Clone W) (hi : L.U={i}) (s : W → Bool) (f : Clause F) :
    (factorAt (N1.δ R Q : ℤ) (literalRead L hreg (N1.δ R Q) R i) s f).value.intSize ≤
      N1.A W R Q BP^N1.arity f := by
  rw [literal_factor_same L bounds i hi s f]
  exact (intCapture_le_norm _).trans (N1.norm_factor L hreg bounds _ s f)

#print axioms factorAt_ops
#print axioms paidProduct_ops
#print axioms paidProduct_guarded_width
#print axioms intCapture_le_norm
#print axioms literal_factor_same
#print axioms literal_factor_width

end
end J3R61
