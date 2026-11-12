import VerticalStripLLT.CyclicHessenberg.Kernel
import VerticalStripLLT.CyclicHessenberg.Loops

/-! Axiom queries for the currently implemented cyclic Hessenberg interfaces.
The final semantic bridge and positivity endpoints must be added when proved. -/

#print axioms VerticalStripLLT.CyclicHessenberg.Hessenberg.ext
#print axioms VerticalStripLLT.CyclicHessenberg.Hessenberg.oneBased_iff
#print axioms VerticalStripLLT.CyclicHessenberg.orderFintype
#print axioms VerticalStripLLT.CyclicHessenberg.ordersEquiv
#print axioms VerticalStripLLT.CyclicHessenberg.isOrder_append_left_iff
#print axioms VerticalStripLLT.CyclicHessenberg.isOrder_append_right_iff
#print axioms VerticalStripLLT.CyclicHessenberg.isOrder_swapAdjacent
#print axioms VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.prefixKernel
#print axioms VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.suffixKernel
#print axioms VerticalStripLLT.CyclicHessenberg.ListExchangeCompatible.minimumDifference
#print axioms VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.diagonal_contextualBalance
#print axioms VerticalStripLLT.CyclicHessenberg.loopColoringLLT
#print axioms VerticalStripLLT.CyclicHessenberg.loopColoringLLT_empty
#print axioms VerticalStripLLT.CyclicHessenberg.loopColoringLLT_zero_alphabet
#print axioms VerticalStripLLT.CyclicHessenberg.colorPrecedes_of_lt
#print axioms VerticalStripLLT.CyclicHessenberg.colorPrecedes_of_gt
