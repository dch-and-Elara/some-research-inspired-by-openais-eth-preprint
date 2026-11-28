import J6R12BlueprintFactory
import J6R10ProbeFieldZero

set_option warningAsError true
namespace Paper5.OuterCenters
open scoped Polynomial
open J6R12Blueprint J6R11Blueprint J6ActiveRun J6R9Recursive

/-- If the legal probe list contains zero at an address, the source's
actual packet dispatch is exactly the child whose local variable is zero. -/
theorem source_packet_address_at_zero {f : ℤ[X]} {ell Δ : ℕ}
    {S : Params (f:=f) (ell:=ell)} {c : Call (H (f:=f) (ell:=ell))}
    (sel : Selector S Δ) (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : SiteMode sel d t →₀ ℕ) (g : Fin 64)
    (hz : sampleNode S f ell c d.fit t z = 0) :
    letI := c.host.finiteEdge
    letI := c.host.finiteRow
    letI := c.host.finiteCol
    let p := registerPrecision S c t
    packetOfSite sel d t z β g =
      actualPacketHost (packing sel d) (centerIndex d t) (centerNonzero t) rfl
        p (J6R10Integral.box_two_nil p f ell) 0 c.host.file β g := by
  simp [packetOfSite, hz]

#print axioms source_packet_address_at_zero
#print axioms J6R10ProbeFieldZero.zero_in_uniform_menu
end Paper5.OuterCenters
