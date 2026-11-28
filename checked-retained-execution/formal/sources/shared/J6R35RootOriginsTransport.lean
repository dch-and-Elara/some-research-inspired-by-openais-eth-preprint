import J6R21AncestorRun

/-! Generic *dependent* geometry transport for a zero-mode point.
The physical page is coerced only along two proved shape equalities;
there is no finite-cardinality relabelling. -/
namespace J6R35RootOrigins
open scoped Polynomial
open Polynomial J6R21Ancestor J6R10Repack J6R11Blueprint
open P11FullPacking J6R9PacketScopes
set_option maxHeartbeats 12000000
set_option maxRecDepth 2000

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G]
variable {N : Network E A B} {a₀ a₁ : ℕ}

def packAxis (P : PhysicalPacking N a₀ G) (e : a₀=a₁) :
    PhysicalPacking N a₁ G :=
  cast (congrArg (fun a=>PhysicalPacking N a G) e) P

def packPageCongr (e : a₀=a₁) (P : PhysicalPacking N a₀ G)
    (P' : PhysicalPacking N a₁ G) (shape : P'=packAxis P e) :
    Page a₀ P.copies G ≃ Page a₁ P'.copies G := by
  subst a₁
  subst P'
  exact Equiv.refl _

theorem transport_zero_page {f : ℤ[X]} {ell p q : ℕ}
    (e : a₀=a₁) (ep : p=q) (P : PhysicalPacking N a₀ G)
    (P' : PhysicalPacking N a₁ G) (shape : P'=packAxis P e)
    (i : Fin a₁) (j : Fin a₀) (axis : i.val=j.val)
    {t u : ℤ} (time : t=u) (ht : t≠0) (hu : u≠0)
    (vi : padicValInt 2 t=i.val) (vj : padicValInt 2 u=j.val)
    (z : Residue f ell p) (z' : Residue f ell q)
    (node : cast (congrArg (Residue f ell) ep) z=z')
    (file : EntryFile f ell N) (g : G) (k : Page a₀ P.copies G) :
    generatedPoint P' i ht vi z file 0 g (packPageCongr e P P' shape k) =
      generatedPoint P j hu vj z' file 0 g k := by
  subst a₁
  subst P'
  subst q
  subst u
  have eq : i=j := Fin.ext axis
  subst j
  have same : z=z' := node
  subst z'
  rfl

end J6R35RootOrigins
#print axioms J6R35RootOrigins.packPageCongr
#print axioms J6R35RootOrigins.transport_zero_page
