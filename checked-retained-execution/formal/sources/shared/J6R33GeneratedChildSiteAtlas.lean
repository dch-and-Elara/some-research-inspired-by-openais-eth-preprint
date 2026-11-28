import J6R33GeneratedChildSitePage
import J6R33PageIndexedBirthAtlas

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2700
set_option maxHeartbeats 17500000

/-! Compose the generated child event with the paid complete ordered
page atlas. Local compiler success and its cost come from the exact
installed chart, not from caller-supplied page fields or success flags. -/
namespace J6R33GeneratedChildSite
open scoped Polynomial Classical
open AOracleMachineTime AOracleMachineTimeTape A1R10 J6R15ModeCost J6R27OriginalGate
open J6R30ProducedGateRegistry J6R33PageIndexedBirth J6R32ChildResidentTransfer
open J6R10Repack P11FullPacking J6R16ModeCost J6R21Ancestor J6R20Ancestor J6R9Recursive

def runSiteAtlas {a q p ell code tw bw : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (R : ChildResidents a q) (X : ActiveWords fw (q+1) tw bw)
    (hp : 0<p) (hv : 0<ell) (fit : i.val+1≤q+1) :
    Meter (Option (CentreContext tw bw×List (PageRow a p ell (q+1) ((q-a)+13*a) fw i))) :=
  let input := prepareSite code R X
  match input.result with
  | none=>⟨none,input.steps+3⟩
  | some (ctx,C)=>
    let all := compileAtlas C hp hv fit (Nat.succ_pos q) R.raw.copies
    ⟨all.result.map (fun x=>(ctx,x)),input.steps+all.steps+6⟩

def runSiteRows {a q p ell code tw bw : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (R : ChildResidents a q) (X : ActiveWords fw (q+1) tw bw)
    (hp : 0<p) (hv : 0<ell) (fit : i.val+1≤q+1) :
    Meter (Option (List (PageRow a p ell (q+1) ((q-a)+13*a) fw i))) :=
  let x := runSiteAtlas (code:=code) R X hp hv fit
  ⟨x.result.map Prod.snd,x.steps+3⟩

variable {E A B : Type} {N : Network E A B} {a q p ell code tw bw : ℕ}
  {P : PhysicalPacking N a (Fin 64)} {i : Fin a} {R : ChildResidents a q}
variable (H : ResidentReceipt P i p R) {fw : List (A1R10.Word p)}
variable {f : ℤ[X]}
variable [DecidableEq (Page a P.copies (Fin 64))]

noncomputable abbrev runFee : ℕ :=
  prepareSiteFee a q i.val fw.length code tw bw H.modes.length+
    requestsFee a (q-a) (q+1) P.copies+
    pagesCount a P.copies*(sitePageFee (ell:=ell) (code:=code) (fw:=fw) H+
      onePageFee ((q-a)+13*a)+5)+12

structure AtlasReceipt (X : ActiveWords fw (q+1) tw bw)
    (hp : 0<p) (hv : 0<ell) (fit : i.val+1≤q+1)
    (hMod : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (node : Box f ell p) (g : Fin 64) (β : Legal P i p) where
  page : ∀ k : Page a P.copies (Fin 64), PageReceipt H (commonView code R X) hp hv fit hMod node g β k
  bank : List (PageRow a p ell (q+1) ((q-a)+13*a) fw i)
  order : bank=(orderedChildPages a P.copies).map (fun k=>⟨childPageKey (q-a) k,(page k).fields⟩)
  success : (runSiteAtlas (code:=code) R X hp hv fit).result=some (X.context,bank)
  rowsReady : (runSiteRows (code:=code) R X hp hv fit).result=some bank
  keysUnique : (bank.map RefRow.address).Nodup
  lookup : ∀ k,(locate (childPageKey (q-a) k) bank).result=some (page k).fields
  fee : (runSiteAtlas (code:=code) R X hp hv fit).steps≤
    runFee (ell:=ell) (code:=code) (tw:=tw) (bw:=bw) (fw:=fw) H
  rowsFee : (runSiteRows (code:=code) R X hp hv fit).steps≤
    runFee (ell:=ell) (code:=code) (tw:=tw) (bw:=bw) (fw:=fw) H+3

theorem actual_child_paged_atlas {n : ℕ} (X : ActiveWords fw (q+1) tw bw)
    (clock : X.axis.length=i.val) (g : Fin 64) (hG : X.group.val=g.val)
    (codePos : 0<code) (codeFit : 1+H.modes.length<2^code)
    (β : Legal P i p)
    (hβ : X.exponents.map Word.val=H.modes.map (fun m=>β.val ((packet_mode_equiv P.mask i p).symm m)))
    (hp : 0<p) (hv : 0<ell) (fit : i.val+1≤q+1)
    (hMod : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (probeFit : n≤2^f.natDegree) (z : Fin n)
    (hZ : X.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree n probeFit z)) :
    Nonempty (AtlasReceipt (code:=code) H X hp hv fit hMod
      (J6ActiveInterpolation.node p f ell n probeFit z) g β) := by
  let C := commonView code R X
  let node := J6ActiveInterpolation.node p f ell n probeFit z
  let pageResult k : PageReceipt H C hp hv fit hMod node g β k :=
    Classical.choice (fixed_page_compiles H X clock g hG codePos codeFit β hβ hp hv fit hMod probeFit z hZ k)
  let F := fun k=>(pageResult k).fields
  let bank := (orderedChildPages a P.copies).map
    (fun k=>(⟨childPageKey (q-a) k,F k⟩ : PageRow a p ell (q+1) ((q-a)+13*a) fw i))
  let fPage := sitePageFee (ell:=ell) (code:=code) (fw:=fw) H
  obtain ⟨result,unique,lookup,price⟩ := compile_atlas_exact (maxFee:=fPage)
    C hp hv fit (Nat.succ_pos q) R.raw.copies H.copyValue H.copiesFit F
    (fun k=>(pageResult k).hit) (fun k=>(pageResult k).fee)
  have len : X.exponents.length=H.modes.length := by
    simpa only [List.length_map] using congrArg List.length hβ
  have prep := prepare_site_exact (code:=code) H X clock len
  let O := runSiteAtlas (code:=code) R X hp hv fit
  have R0 : O.result=some (X.context,bank) := by
    unfold O runSiteAtlas
    dsimp only
    rw [prep]
    change ((compileAtlas C hp hv fit (Nat.succ_pos q) R.raw.copies).result.map
      (fun x=>(X.context,x)))=_
    rw [result]
    rfl
  have Fee : O.steps≤runFee (ell:=ell) (code:=code) (tw:=tw) (bw:=bw) (fw:=fw) H := by
    unfold O runSiteAtlas
    dsimp only
    rw [prep]
    change prepareSiteFee a q i.val fw.length code tw bw H.modes.length+
      (compileAtlas C hp hv fit (Nat.succ_pos q) R.raw.copies).steps+6≤_
    unfold runFee
    change (compileAtlas C hp hv fit (Nat.succ_pos q) R.raw.copies).steps≤_ at price
    dsimp only [fPage] at price
    omega
  refine ⟨⟨pageResult,bank,rfl,R0,?_,unique,lookup,Fee,Nat.add_le_add_right Fee 3⟩⟩
  change O.result.map Prod.snd=_
  rw [R0]
  rfl

#print axioms actual_child_paged_atlas
end J6R33GeneratedChildSite
