import V8NativeMessageN6MainTied
import V8NativeMessageN6MainColor

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6200000

/-! Untied v8 N6. A cut of whole source factor groups crosses at
least half the split triangles. On the selected slice the entire
completed jet (before the single readout) is a product of two jets. -/
namespace V8NativeMessage.N6
open scoped Classical BigOperators Polynomial
open Paper5.HybridClosure V8CapacityUnified.U7
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {V : Type*} [Fintype V]
variable {G : Type*} [DecidableEq G]

def splitTriangles (owner : TriVertex V→G) : Finset V :=
  Finset.univ.filter (fun v => ∃ a b : Fin 3, owner (v,a)≠owner (v,b))

theorem has_two_groups (owner : TriVertex V→G) (v : splitTriangles owner) :
    ∃ a b : Fin 3, owner (v.val,a)≠owner (v.val,b) :=
  (Finset.mem_filter.mp v.property).2

def splitLeft (owner : TriVertex V→G) (v : splitTriangles owner) : Fin 3 :=
  Classical.choose (has_two_groups owner v)

def splitRight (owner : TriVertex V→G) (v : splitTriangles owner) : Fin 3 :=
  Classical.choose (Classical.choose_spec (has_two_groups owner v))

theorem split_pairs_distinct (owner : TriVertex V→G) (v : splitTriangles owner) :
    owner (v.val,splitLeft owner v)≠owner (v.val,splitRight owner v) :=
  Classical.choose_spec (Classical.choose_spec (has_two_groups owner v))

abbrev CutSites (owner : TriVertex V→G) (χ : G→Bool) :=
  {v : splitTriangles owner // χ (owner (v.val,splitLeft owner v)) ≠
    χ (owner (v.val,splitRight owner v))}

def cutIndex (owner : TriVertex V→G) (χ : G→Bool) :
    Fin (Fintype.card (CutSites owner χ)) ≃ CutSites owner χ :=
  (Fintype.equivFin _).symm

def cutSlice (owner : TriVertex V→G) (χ : G→Bool) :
    TriangleSlice V (Fintype.card (CutSites owner χ)) where
  vertex := (cutIndex owner χ).toEmbedding.trans
    (⟨Subtype.val,Subtype.val_injective⟩ : CutSites owner χ ↪ splitTriangles owner) |>.trans
    ⟨Subtype.val,Subtype.val_injective⟩
  left i :=
    let v := ((cutIndex owner χ) i).val
    if χ (owner (v.val,splitLeft owner v)) then splitLeft owner v else splitRight owner v
  right i :=
    let v := ((cutIndex owner χ) i).val
    if χ (owner (v.val,splitLeft owner v)) then splitRight owner v else splitLeft owner v
  distinct i := by
    let v := ((cutIndex owner χ) i).val
    have hn : splitLeft owner v≠splitRight owner v := by
      intro h
      exact split_pairs_distinct owner v (congrArg (fun j => owner (v.val,j)) h)
    change (if χ (owner (v.val,splitLeft owner v)) then splitLeft owner v else splitRight owner v) ≠
      (if χ (owner (v.val,splitLeft owner v)) then splitRight owner v else splitLeft owner v)
    cases χ (owner (v.val,splitLeft owner v)) <;> simp [hn,hn.symm]

theorem cutSlice_seated (owner : TriVertex V→G) (χ : G→Bool)
    (i : Fin (Fintype.card (CutSites owner χ))) :
    χ (owner (leftPin (cutSlice owner χ) i))=true ∧
      χ (owner (rightPin (cutSlice owner χ) i))=false := by
  let v := ((cutIndex owner χ) i).val
  have hd : χ (owner (v.val,splitLeft owner v))≠χ (owner (v.val,splitRight owner v)) :=
    ((cutIndex owner χ) i).property
  change χ (owner (v.val,if χ (owner (v.val,splitLeft owner v)) then splitLeft owner v else splitRight owner v))=true ∧
    χ (owner (v.val,if χ (owner (v.val,splitLeft owner v)) then splitRight owner v else splitLeft owner v))=false
  cases ha : χ (owner (v.val,splitLeft owner v)) <;>
    cases hb : χ (owner (v.val,splitRight owner v)) <;> simp_all

variable [Fintype G]

/-- One honest group cut and one consistently oriented pair in every
counted triangle; the triangle sites themselves are distinct. -/
theorem split_has_slice (owner : TriVertex V→G) :
    ∃ (χ : G→Bool) (m : ℕ) (s : TriangleSlice V m),
      (splitTriangles owner).card ≤ 2*m ∧
      (∀ i, χ (owner (leftPin s i))=true) ∧ (∀ i, χ (owner (rightPin s i))=false) := by
  obtain ⟨χ,hχ⟩ := half_cut (fun v : splitTriangles owner => owner (v.val,splitLeft owner v))
    (fun v : splitTriangles owner => owner (v.val,splitRight owner v)) (split_pairs_distinct owner)
  exact ⟨χ,Fintype.card (CutSites owner χ),cutSlice owner χ,
    by simpa only [Fintype.card_coe] using hχ,
    fun i => (cutSlice_seated owner χ i).1, fun i => (cutSlice_seated owner χ i).2⟩

section Literal
variable [DecidableEq V]
variable {F : Finset (TriVertex V×TriVertex V)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J) (cubic : ∀ v, GraphCutMoments.degree F v=3)
  (h : feasible L.frame) (P : FixedLists L)

def colorJet (χ : Fin r→Bool) (side : Bool) (σ : TriVertex V→Bool) : Jet J :=
  ∏ g, if χ g=side then groupJet L cubic h P g σ else 1

theorem completed_by_colored_groups {m : ℕ} (s : TriangleSlice V m) (χ : Fin r→Bool)
    (hl : ∀ i, χ (pinGroup L (leftPin s i))=true)
    (hr : ∀ i, χ (pinGroup L (rightPin s i))=false)
    (x y : Fin m→Bool) :
    completed L cubic h P (word s x y) =
      colorJet L cubic h P χ true (word s x (fun _=>true)) *
      colorJet L cubic h P χ false (word s (fun _=>true) y) := by
  unfold completed colorJet
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  cases hc : χ g with
  | false =>
    simp only [Bool.false_eq_true,ite_false,ite_true,one_mul]
    apply groupJet_pin_local
    intro v hv
    exact word_cross_right s x y (χ ∘ pinGroup L) hl v (by simpa only [Function.comp_apply,hv] using hc)
  | true =>
    simp only [Bool.true_eq_false,ite_false,ite_true,mul_one]
    apply groupJet_pin_local
    intro v hv
    exact word_cross_left s x y (χ ∘ pinGroup L) hr v (by simpa only [Function.comp_apply,hv] using hc)

/-- Exact finite form of splitTriangles ≤ 2 log₂ J, including all
fixed weighted private lists. A single full group product, rather
than its lists expanded term by term, is cut. -/
theorem N6_untied (read : Jet J→ₗ[ℚ]ℚ)
    (correct : ∀ σ, read (completed L cubic h P σ)=UM σ) :
    2^(((splitTriangles (pinGroup L)).card+1)/2)≤J := by
  obtain ⟨χ,m,s,hm,hl,hr⟩ := split_has_slice (pinGroup L)
  let a (x : Fin m→Bool) := colorJet L cubic h P χ true (word s x (fun _=>true))
  let b (y : Fin m→Bool) := colorJet L cubic h P χ false (word s (fun _=>true) y)
  have fact : C3.mixedTerm read a b (fun _=>1) (fun _=>1) = matchingTarget ℚ m := by
    ext x y
    simp only [C3.mixedTerm,Matrix.of_apply,mul_one]
    change read (a x*b y)=_
    rw [← completed_by_colored_groups L cubic h P s χ hl hr x y]
    exact (correct _).trans (UM_on_slice s x y)
  have cap := read_rank read a b
  rw [fact,matching_full_rank] at cap
  exact (Nat.pow_le_pow_right (by decide) (show ((splitTriangles (pinGroup L)).card+1)/2≤m by omega)).trans cap

include h in
theorem N6_untied_source (read : Jet J→ₗ[ℚ]ℚ)
    (correct : ∀ σ, read (nativeScan F cubic L σ).2.2=UM σ) :
    2^(((splitTriangles (pinGroup L)).card+1)/2)≤J := by
  apply N6_untied L cubic h (exhaustive L) read
  intro σ
  rw [exhaustive_completed L cubic h]
  exact correct σ

end Literal

#print axioms split_pairs_distinct
#print axioms cutSlice_seated
#print axioms split_has_slice
#print axioms completed_by_colored_groups
#print axioms N6_untied
#print axioms N6_untied_source

end
end V8NativeMessage.N6
