import J3R61Factors

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000

/-! Exact native constant and first coefficient from the executed signed
factor product. Degrees and the common denominator are also accumulated by
explicit loops. A subset is useful for the graph-only public product. -/
namespace J3R61
open Polynomial V8NativeMessage
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open J3R38LiteralSingleton
open scoped BigOperators Polynomial Classical

def factorDegrees {W : Type*} {F : Finset (W×W)} : List (Clause F) → Paid ℕ
  | [] => ⟨0,0⟩
  | f :: fs =>
    let g := factorDegrees fs
    ⟨N1.arity f+g.value,g.ops+1⟩

theorem factorDegrees_exact {W : Type*} {F : Finset (W×W)} (fs : List (Clause F)) :
    (factorDegrees fs).value = (fs.map N1.arity).sum ∧ (factorDegrees fs).ops = fs.length := by
  induction fs with
  | nil => exact ⟨rfl,rfl⟩
  | cons f fs ih => simp only [factorDegrees,List.map_cons,List.sum_cons,List.length_cons,ih.1,ih.2,and_self]

def powerLoop (D : ℕ) : ℕ → Paid ℕ
  | 0 => ⟨1,0⟩
  | d+1 =>
    let r := powerLoop D d
    ⟨r.value*D,r.ops+1⟩

theorem powerLoop_exact (D d : ℕ) :
    (powerLoop D d).value=D^d ∧ (powerLoop D d).ops=d := by
  induction d with
  | zero => exact ⟨rfl,rfl⟩
  | succ d ih => simp only [powerLoop,ih.1,ih.2,pow_succ,and_self]

def rationalPair (p : Pair ℤ) (D : ℕ) : Pair ℚ :=
  ⟨(p.c:ℚ)/(D:ℚ),(p.d:ℚ)/(D:ℚ)⟩

noncomputable def jetTwo {J : ℕ} (q : Jet J) : Pair ℚ :=
  ⟨J3R38LiteralSingleton.jetCoeff 0 q,J3R38LiteralSingleton.jetCoeff 1 q⟩

theorem captured_scaled_jet {J : ℕ} (hJ : 2 ≤ J) (d : ℕ) (hd : 0<d) (p : ℤ[X]) (v : Jet J)
    (lift : N1.jetify J p=(d:Jet J)*v) :
    rationalPair (capture p) d = jetTwo v := by
  have hs (k : ℕ) (hk : k<J) : ((p.coeff k : ℤ) : ℚ)/(d:ℚ) = N1.jetCoeff J k v := by
    apply (div_eq_iff (Nat.cast_ne_zero.mpr hd.ne')).mpr
    rw [← N1.jetify_coeff J k hk, lift, N1.jetCoeff_scale, mul_comm]
  exact Pair.ext' (hs 0 (by omega)) (hs 1 (by omega))

noncomputable section
variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

def degreeOn (S : Finset (Clause F)) : ℕ := ∑ f ∈ S, N1.arity f

def signedRun (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) (s : W → Bool) (S : Finset (Clause F)) : Paid (Pair ℚ) :=
  let d := printedScale R Q
  let t := N1.tInt L
  let read := fun o : N1.Occ F => evalRow (coords W) (N1.row L hreg o) d.value R t i
  let ex := factorDegrees S.toList
  let p := paidProduct (S.toList.map (factorAt (d.value:ℤ) read s))
  let den := powerLoop d.value ex.value
  ⟨rationalPair p.value den.value, d.ops+1+ex.ops+p.ops+den.ops+2⟩

theorem signedRun_exact (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (hJ : 2 ≤ J) (i : Clone W) (hi : L.U={i}) (s : W → Bool) (S : Finset (Clause F)) :
    (signedRun L hreg R i s S).value =
      jetTwo (∏ f ∈ S, cloneFactor F hreg L s (fun _=>true) f) := by
  let p (f : Clause F) := N1.intFactor L hreg bounds s (fun _=>true) f
  have HP : (paidProduct (S.toList.map
      (factorAt (N1.δ R Q:ℤ) (literalRead L hreg (N1.δ R Q) R i) s))).value =
      capture (∏ f ∈ S,p f) := by
    rw [paidProduct_value,List.map_map]
    have he : (Paid.value ∘ factorAt (N1.δ R Q:ℤ)
        (literalRead L hreg (N1.δ R Q) R i) s) = capture ∘ p := by
      funext f
      exact literal_factor_same L bounds i hi s f
    rw [he,← List.map_map,product_actual_coeffs,Finset.prod_map_toList]
  have hD : (factorDegrees S.toList).value = degreeOn S := by
    rw [(factorDegrees_exact _).1,Finset.sum_map_toList,degreeOn]
  change rationalPair (paidProduct (S.toList.map (factorAt ((printedScale R Q).value:ℤ)
      (literalRead L hreg (printedScale R Q).value R i) s))).value
      (powerLoop (printedScale R Q).value (factorDegrees S.toList).value).value = _
  rw [(printedScale_exact R Q).1,hD,(powerLoop_exact _ _).1,HP]
  apply captured_scaled_jet hJ _ (Nat.pow_pos (N1.δ_pos R Q))
  simp only [p,degreeOn,map_prod,N1.jetify_factor,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum,Nat.cast_pow]

theorem signedRun_ops (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (i : Clone W) (s : W → Bool) (S : Finset (Clause F)) :
    (signedRun L hreg R i s S).ops ≤ (R-1)+Q+1+3+(rowOps R (4*Fintype.card W)+10)*degreeOn S := by
  let d := printedScale R Q
  let rows := literalRead L hreg d.value R i
  let a := N1.arity (F:=F)
  let cost (f : Clause F) := (rowOps R (4*Fintype.card W)+8)*a f
  have hr (o : N1.Occ F) : (rows o).ops = rowOps R (4*Fintype.card W) :=
    literalRow_ops L hreg i o
  have hp := paidProduct_ops (factorAt (d.value:ℤ) rows s) cost S.toList
    (fun f => factorAt_ops _ _ _ f _ hr)
  have hcost : (S.toList.map cost).sum = (rowOps R (4*Fintype.card W)+8)*degreeOn S := by
    rw [Finset.sum_map_toList,degreeOn,Finset.mul_sum]
  rw [hcost] at hp
  have hD : (factorDegrees S.toList).value = degreeOn S := by
    rw [(factorDegrees_exact _).1,Finset.sum_map_toList,degreeOn]
  have hsz : S.card ≤ degreeOn S := by
    unfold degreeOn
    calc
      _ = ∑ _f ∈ S,(1:ℕ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        rintro (v|f) _
        · exact le_rfl
        · change 1 ≤ 2
          decide
  have hL : (factorDegrees S.toList).ops = S.card := by rw [(factorDegrees_exact _).2,Finset.length_toList]
  change d.ops+1+(factorDegrees S.toList).ops+(paidProduct (S.toList.map
    (factorAt (d.value:ℤ) rows s))).ops+(powerLoop d.value (factorDegrees S.toList).value).ops+2 ≤ _
  rw [(printedScale_exact R Q).2,hL,(powerLoop_exact _ _).2,hD]
  have hh : (rowOps R (4*Fintype.card W)+10)*degreeOn S =
      (rowOps R (4*Fintype.card W)+8)*degreeOn S + 2*degreeOn S := by ring
  rw [hh]
  omega

theorem signed_product_suffix_width (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (i : Clone W) (hi : L.U={i}) (s : W → Bool) (S : Finset (Clause F)) (k : ℕ) :
    let fs := S.toList.drop k
    let p := paidProduct (fs.map (factorAt (N1.δ R Q:ℤ) (literalRead L hreg (N1.δ R Q) R i) s))
    p.value.intSize ≤ N1.A W R Q BP^((fs.map N1.arity).sum) :=
  paidProduct_guarded_width _ _ _ _ (literal_factor_width L bounds i hi s)

#print axioms factorDegrees_exact
#print axioms powerLoop_exact
#print axioms captured_scaled_jet
#print axioms signedRun_exact
#print axioms signedRun_ops
#print axioms signed_product_suffix_width

end
end J3R61
