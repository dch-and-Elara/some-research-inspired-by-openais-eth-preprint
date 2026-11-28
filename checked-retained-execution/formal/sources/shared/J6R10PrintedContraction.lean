import J6R10GroupAssembly

namespace J6R10PrintedContraction
open scoped Classical BigOperators
open J6ActiveAllocation J6ActiveProfile J6BlockFactor J6ChildIdentity J6SourceMoment
open J6NoOversizedChild J6R10PacketAssembly J6R10GroupAssembly
variable {R P M G K : Type*} [CommRing R] [Fintype P] [Fintype M]
  [Fintype G] [Fintype K]
  {V : G → Type*} [∀ g, Fintype (V g)] [∀ g, Inhabited (V g)]

/-- From the signed rows to the *printed* Finsupp mode menu and concrete
packet coefficients. The only row premises are pointwise affine equality
and target locality; the child contraction equality is proved, not assumed. -/
theorem exact_source_contraction
    (w : M → ℕ) (hw : ∀ m, 0 < w m) (p : ℕ) (hp : (2:R)^p = 0)
    (block : P → G × K) (target source : M → G × K)
    (row : ∀ i, V (block i).1 → Option M → R)
    (old : ∀ g, V g → R) (L : ∀ m, V (source m).1 → R)
    (bit : ∀ g, V g → P → Bool) (base : ∀ g, V g → P → R)
    (cross : ∀ g, V g → P → M → R)
    (hzero : ∀ i m v, block i ≠ target m → row i v (some m) = 0)
    (h0 : ∀ g (y : V g) i (e : (block i).1 = g),
      scaled w (fun _ v => row i (e.symm ▸ y) v) i none =
        LiteralPortCompiler.affine (bit g y i) (base g y i))
    (hm : ∀ g (y : V g) i (e : (block i).1 = g) m,
      scaled w (fun _ v => row i (e.symm ▸ y) v) i (some m) =
        LiteralPortCompiler.slope (bit g y i) * cross g y i m) :
    (∑ x : ∀ g, V g, (∏ g, old g (x g)) *
      (∏ i, ∑ v : Option M, scaled w
        (insert (fun i => row i (x (block i).1)) (fun m => L m (x (source m).1))) i v)) =
    ∑ beta ∈ J6RecursiveMenu.menu p w,
      ∏ g, J6RecursiveModes.child target source (actualRows block) old bit base cross
        (fun g y m => if h : (source m).1 = g then L m (h.symm ▸ y) else 0) beta g := by
  classical
  let L' (g : G) (y : V g) (m : M) : R :=
    if h : (source m).1 = g then L m (h.symm ▸ y) else 0
  let term (beta : M →₀ ℕ) : R :=
    ∏ g, J6RecursiveModes.child target source (actualRows block) old bit base cross L' beta g
  refine (exact_grouped_mode_contraction w p hp block target Prod.fst
    (Prod.fst ∘ source) row old L hzero).trans ?_
  change _ = ∑ beta ∈ J6RecursiveMenu.menu p w, term beta
  refine Eq.trans ?_ (J6ProfileMenu.extend_to_printed (I:=P) w hw p term (fun beta h => ?_))
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : profileWeight w b < p
    · simp only [if_pos hb]
      refine Finset.prod_congr rfl (fun g _ => ?_)
      convert (exact_one_child w block target source row old L bit base cross hzero h0 hm b g) using 1
      apply Finset.sum_congr rfl
      intro y _
      have hM :
          (∏ m : rows (Prod.fst ∘ source) g,
            L m.val (@Eq.rec G g (fun g' _ => V g') y ((Prod.fst ∘ source) m.val) m.property.symm) ^ (b m.val).val) =
          ∏ m : rows (Prod.fst ∘ source) g,
            L m.val (cast (congrArg V m.property.symm) y) ^ (b m.val).val := by
        apply Finset.prod_congr rfl
        rintro ⟨m,e⟩ _
        change (source m).1 = g at e
        subst g
        rfl
      have hK :
          (∏ k : rows (Prod.fst : G × K → G) g,
            localizedCoeff w block target Prod.fst row b k.val (@Eq.rec G g (fun g' _ => V g') y k.val.1 k.property.symm)) =
          ∏ k : rows (Prod.fst : G × K → G) g,
            localizedCoeff w block target Prod.fst row b k.val (cast (congrArg V k.property.symm) y) := by
        apply Finset.prod_congr rfl
        rintro ⟨⟨g',k⟩,e⟩ _
        change g' = g at e
        subst g'
        rfl
      rw [hM,hK]
    · simp only [if_neg hb]
  · exact oversized_child_product_zero target source (actualRows block) old bit base cross L' beta h

#print axioms exact_source_contraction
end J6R10PrintedContraction
