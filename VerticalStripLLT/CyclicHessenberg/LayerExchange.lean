import VerticalStripLLT.CyclicHessenberg.LayerListBridge
import VerticalStripLLT.CyclicHessenberg.ExchangeMatrix

/-! The original transfer layers satisfy scalar exchange, hence so does their ordered product. -/

namespace VerticalStripLLT.CyclicHessenberg

/-- Full spectator-aware exchange for the original positional layer kernel. -/
theorem layerKernelAt_exchangeCompatible {k : ℕ} {R : Type*} [CommSemiring R]
    (h : Hessenberg k) (q : R) : ExchangeCompatible q (layerKernelAt h (1 + q)) := by
  have heq : layerKernelAt h (1 + q) =
      fun π τ : FullOrder k => layerListWeight h q π.val τ.val := by
    funext π τ
    exact (layerListWeight_eq h q π τ).symm
  rw [heq]
  exact (layerListWeight_exchangeCompatible h h.monotone q).toKernel Finset.univ

theorem naturalLayerKernel_exchangeCompatible {k : ℕ} (h : Hessenberg k) :
    ExchangeCompatible Polynomial.X (naturalLayerKernel h) :=
  layerKernelAt_exchangeCompatible h Polynomial.X

/-- The independently defined product of natural layer matrices preserves exchange. -/
theorem naturalOpenKernel_exchangeCompatible {k n : ℕ} (h : Tuple k n) :
    ExchangeCompatible Polynomial.X (naturalOpenKernel h) := by
  apply ExchangeCompatible.list_prod
  intro Z hZ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hZ
  exact naturalLayerKernel_exchangeCompatible (h i)

/-- This is the same single shift as in the raw product, with compatibility proved by casting. -/
theorem shiftedRawOpenKernel_exchangeCompatible {k n : ℕ} (h : Tuple k n) :
    ExchangeCompatible Polynomial.X (VerticalStripLLT.qShift.mapMatrix (rawOpenKernel h)) := by
  rw [← cast_naturalOpenKernel_eq_shift_rawOpenKernel]
  have hh := (naturalOpenKernel_exchangeCompatible h).map naturalPolynomialCast
  simpa [naturalPolynomialCast] using hh

end VerticalStripLLT.CyclicHessenberg
