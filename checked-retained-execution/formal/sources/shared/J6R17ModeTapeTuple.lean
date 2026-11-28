import J6R16ModeCostCatalog
import Mathlib.Data.List.NodupEquivFin

/-! Reverse the previous cardinal injection: the complete roster
gives exactly one native sparse exponent for each emitted legal
vector. The inverse is only for the correctness statement; the
raw dispatch scans addresses and exponents in lockstep. -/
namespace J6R17ModeTape
open scoped Classical Polynomial
open J6R15ModeCost J6R16ModeCost J6ActiveRun J6R12Blueprint J6R11Blueprint J6R10Reachable

theorem exponentVector_unique {A : Type*} [Finite A] [DecidableEq A]
    (ms : List A) (hn : ms.Nodup) (ha : ∀ m,m∈ms)
    (es : List ℕ) (hL : es.length=ms.length) :
    ∃! β : A→₀ ℕ, ms.map β=es := by
  let ι := List.Nodup.getEquivOfForallMemList ms hn ha
  let f : A→ℕ := fun a=>es.get (Fin.cast hL.symm (ι.symm a))
  let β := Finsupp.equivFunOnFinite.symm f
  have hB (a : A) : β a=f a :=
    congrFun (Finsupp.equivFunOnFinite.apply_symm_apply f) a
  have hRaw : ms.map (fun a => β a)=es := by
    apply List.ext_getElem (by simpa only [List.length_map] using hL.symm)
    intro j hj hk
    rw [List.getElem_map,hB]
    let k : Fin ms.length := ⟨j,by simpa only [List.length_map] using hj⟩
    change es.get (Fin.cast hL.symm (ι.symm (ι k)))=es[j]
    rw [Equiv.symm_apply_apply]
    rfl
  refine ⟨β,hRaw,?_⟩
  intro β' hRaw'
  ext a
  apply List.map_inj_left.mp _ a (ha a)
  exact hRaw'.trans hRaw.symm

theorem exact_legal_vector {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (ξ : A≃B) (w : A→ℕ) (wb : B→ℕ) (hW : ∀ a,w a=wb (ξ a))
    (hP : ∀ b,0<wb b)
    (ms : List B) (hm : ms.Nodup) (ha : ∀ m,m∈ms) (p : ℕ) (es : List ℕ) :
    es∈strictTuples (ms.map wb) p ↔
      ∃! β : ↑(J6RecursiveMenu.menu p w),ms.map (fun m=>β.val (ξ.symm m))=es := by
  have hPos : ∀ j∈ms.map wb,0<j := by
    intro j hj
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp hj
    exact hP m
  have hPositive : ∀ a,0<w a := fun a=> (hW a).symm ▸ hP (ξ a)
  obtain ⟨_,hS⟩ := strictTuples_exact (ms.map wb) p hPos
  constructor
  · intro H
    obtain ⟨hL,hD⟩ := (hS es).mp H
    let bs := ms.map ξ.symm
    have hb : bs.Nodup := hm.map ξ.symm.injective
    have hB (a : A) : a∈bs := List.mem_map.mpr ⟨ξ a,ha _,ξ.symm_apply_apply a⟩
    obtain ⟨β,hβ,hU⟩ := exponentVector_unique bs hb hB es (by simpa only [bs,List.length_map] using hL)
    have hT : ms.map (fun m=>β (ξ.symm m))=es := by
      simpa only [bs,List.map_map] using hβ
    have hLegal : β∈J6RecursiveMenu.menu p w := by
      apply (J6RecursiveMenu.exact_printed_menu p w hPositive β).mpr
      rwa [← roster_is_menu_weight ξ w wb hW ms hm ha, hT]
    refine ⟨⟨β,hLegal⟩,hT,?_⟩
    intro β' hβ'
    apply Subtype.ext
    apply hU
    simpa only [bs,List.map_map] using hβ'
  · rintro ⟨β,H,_⟩
    apply (hS es).mpr
    refine ⟨?_,?_⟩
    · rw [← H,List.length_map,List.length_map]
    · rw [← H,roster_is_menu_weight ξ w wb hW ms hm ha]
      exact (J6RecursiveMenu.exact_printed_menu p w hPositive β.val).mp β.property

theorem native_tuple_iff {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
    (sel : Selector S Δ) {c : Call (PhysicalHost f ell)}
    (d : Ready S Δ c) (t : Center S c)
    (ms : List (NativeRoster sel d t)) (hm : ms.Nodup) (ha : ∀ m,m∈ms) (es : List ℕ) :
    es∈strictTuples (ms.map modeWeight) (registerPrecision S c t) ↔
      ∃! β : NativeMenu (shape S Δ sel) c t,
        ms.map (fun m=>β.val ((site_mode_equiv sel d t).symm m))=es := by
  letI : Fintype ((shape S Δ sel).Mode c t) := (shape S Δ sel).finiteMode c t
  letI : DecidableEq ((shape S Δ sel).Mode c t) := (shape S Δ sel).decideMode c t
  exact exact_legal_vector (site_mode_equiv sel d t) ((shape S Δ sel).weight c t) modeWeight
    (site_mode_weight sel d t) (fun m=>(modeWeight_bounds m).1) ms hm ha _ es

#print axioms exponentVector_unique
#print axioms exact_legal_vector
#print axioms native_tuple_iff
end J6R17ModeTape

