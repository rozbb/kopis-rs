import Kopis.Properties.GenMatrix
open Aeneas Aeneas.Std Result RustKopisSerial
namespace Kopis.Properties

/-! ## `zeroize::Zeroizing` model (`zeroize` crate trust boundary)

`Zeroizing<Z>` is extracted as an opaque type. Functionally it is a transparent box around one
`Z`: the wipe happens on drop, which Aeneas does not model. `zeroizingVal w` is the boxed value.
Taking `Zeroizing Z := Z` and `zeroizingVal := id` satisfies every axiom below, so they are
consistent. -/

/-- The value a `Zeroizing` box holds. An axiom rather than an `opaque`, since `Z` need not be
inhabited. -/
axiom zeroizingVal {Z : Type} : zeroize.Zeroizing Z → Z

/-- `Zeroizing::new x` boxes `x`. -/
@[step] axiom zeroizing_new_spec {Z : Type} (inst : zeroize.Zeroize Z) (x : Z) :
    zeroize.Zeroizing.new inst x ⦃ (w : zeroize.Zeroizing Z) => zeroizingVal w = x ⦄

/-- `Deref` returns the boxed value. -/
@[step] axiom zeroizing_deref_spec {Z : Type} (inst : zeroize.Zeroize Z) (w : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref inst w ⦃ (x : Z) => x = zeroizingVal w ⦄

/-- `DerefMut` returns the boxed value, and a back function that boxes its argument. -/
@[step] axiom zeroizing_deref_mut_spec {Z : Type} (inst : zeroize.Zeroize Z)
    (w : zeroize.Zeroizing Z) :
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut inst w
      ⦃ ((x : Z), (back : Z → zeroize.Zeroizing Z)) =>
        x = zeroizingVal w ∧ ∀ y, zeroizingVal (back y) = y ⦄

end Kopis.Properties
