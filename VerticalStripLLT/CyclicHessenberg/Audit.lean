import VerticalStripLLT.CyclicHessenberg.Kernel
import VerticalStripLLT.CyclicHessenberg.Loops
import VerticalStripLLT.CyclicHessenberg.ExchangeMatrix
import VerticalStripLLT.CyclicHessenberg.Expansion
import VerticalStripLLT.CyclicHessenberg.Layer
import VerticalStripLLT.CyclicHessenberg.Coloring
import VerticalStripLLT.CyclicHessenberg.LoopKernel
import VerticalStripLLT.CyclicHessenberg.LayerExchangeCounts
import VerticalStripLLT.CyclicHessenberg.ColorInsertion
import VerticalStripLLT.CyclicHessenberg.ColorClassProducts
import VerticalStripLLT.CyclicHessenberg.LayerExchange
import VerticalStripLLT.CyclicHessenberg.LoopSemantics
import VerticalStripLLT.CyclicHessenberg.ColorDeletion
import VerticalStripLLT.CyclicHessenberg.ColorEvaluation
import VerticalStripLLT.CyclicHessenberg.KernelSupport
import VerticalStripLLT.CyclicHessenberg.RecursivePositivity

import VerticalStripLLT.CyclicHessenberg.MatchingExpansion
import VerticalStripLLT.CyclicHessenberg.CycleCoefficients

import VerticalStripLLT.CyclicHessenberg
import VerticalStripLLT.Examples.CyclicHessenberg
import VerticalStripLLT.CyclicHessenberg.ZeroExpansion

/-! Axiom queries for cyclic source semantics, deletion, expansions and coefficient positivity. -/

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
#print axioms VerticalStripLLT.CyclicHessenberg.insertionEquiv
#print axioms VerticalStripLLT.CyclicHessenberg.sum_insertOrder
#print axioms VerticalStripLLT.CyclicHessenberg.exchangeCompatible_iff_commute
#print axioms VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.mul
#print axioms VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.list_prod
#print axioms VerticalStripLLT.CyclicHessenberg.rootDeletion_exchangeCompatible
#print axioms VerticalStripLLT.CyclicHessenberg.signedRootDeletion_eq_rootDeletion
#print axioms VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_add
#print axioms VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_smul
#print axioms VerticalStripLLT.CyclicHessenberg.kernelExpansion_coeff_nonneg
#print axioms VerticalStripLLT.CyclicHessenberg.cast_naturalOpenKernel_eq_shift_rawOpenKernel
#print axioms VerticalStripLLT.CyclicHessenberg.naturalOpenKernel_entry_eq_sum
#print axioms VerticalStripLLT.CyclicHessenberg.orderColoringEnumerator_empty
#print axioms VerticalStripLLT.CyclicHessenberg.orderColoringEnumerator_zero_alphabet
#print axioms VerticalStripLLT.CyclicHessenberg.loopBoundaryPathEquiv
#print axioms VerticalStripLLT.CyclicHessenberg.sortColorOrder_unique
#print axioms VerticalStripLLT.CyclicHessenberg.sortColorOrder_orderEquiv_precedes
#print axioms VerticalStripLLT.CyclicHessenberg.layerAscentCount_eq_sum
#print axioms VerticalStripLLT.CyclicHessenberg.laterSpectatorIndicatorSwap
#print axioms VerticalStripLLT.CyclicHessenberg.contextEq_iff_all_contexts
#print axioms VerticalStripLLT.CyclicHessenberg.repeated_sandwich
#print axioms VerticalStripLLT.CyclicHessenberg.descendingClass_mul_inverseClass
#print axioms VerticalStripLLT.CyclicHessenberg.inverseClass_mul_descendingClass
#print axioms VerticalStripLLT.CyclicHessenberg.descendingClass_conjugate_ad
#print axioms VerticalStripLLT.CyclicHessenberg.wordAd_terminates
#print axioms VerticalStripLLT.CyclicHessenberg.descendingClass_eq_sublistSum
#print axioms VerticalStripLLT.CyclicHessenberg.inverseClass_eq_sublistSum
#print axioms VerticalStripLLT.CyclicHessenberg.colorClassProduct_insert_root
#print axioms VerticalStripLLT.CyclicHessenberg.finite_weight_shift
#print axioms VerticalStripLLT.CyclicHessenberg.layerListWeight_exchangeCompatible
#print axioms VerticalStripLLT.CyclicHessenberg.layerListWeight_eq
#print axioms VerticalStripLLT.CyclicHessenberg.layerKernelAt_exchangeCompatible
#print axioms VerticalStripLLT.CyclicHessenberg.naturalOpenKernel_exchangeCompatible
#print axioms VerticalStripLLT.CyclicHessenberg.shiftedRawOpenKernel_exchangeCompatible
#print axioms VerticalStripLLT.CyclicHessenberg.list_prod_eq_sum_fixedBoundaryPath
#print axioms VerticalStripLLT.CyclicHessenberg.rawOpenKernel_diagonal_eq_closedLayerPath_sum
#print axioms VerticalStripLLT.CyclicHessenberg.loopEventEquiv_mem
#print axioms VerticalStripLLT.CyclicHessenberg.coloredLoopAscentCount_eq_path_sum
#print axioms VerticalStripLLT.CyclicHessenberg.loopColoringLLT_eq_kernelColoringLLT
#print axioms VerticalStripLLT.CyclicHessenberg.colorInsertion_eq_adExpansion
#print axioms VerticalStripLLT.CyclicHessenberg.wordAd_eq_signedSetMountain
#print axioms VerticalStripLLT.CyclicHessenberg.mountainWordSum_eval_positive
#print axioms VerticalStripLLT.CyclicHessenberg.colorInsertion_eq_mountainSum
#print axioms VerticalStripLLT.CyclicHessenberg.colorClassProduct_restrict
#print axioms VerticalStripLLT.CyclicHessenberg.sum_subwords_eq_sum_colorings
#print axioms VerticalStripLLT.CyclicHessenberg.colorClassProduct_eq_positionProduct
#print axioms VerticalStripLLT.CyclicHessenberg.colorClassProduct_eval
#print axioms VerticalStripLLT.CyclicHessenberg.colorClassProduct_eval_of_subset
#print axioms VerticalStripLLT.CyclicHessenberg.SupportedKernel.rootDeletion
#print axioms VerticalStripLLT.CyclicHessenberg.weightedKernelColoring_insert_max
#print axioms
  VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_eval_eq_weightedKernelColoring
#print axioms
  VerticalStripLLT.CyclicHessenberg.xQShift_loopColoringLLT_eq_naturalOpenKernel_coloring
#print axioms VerticalStripLLT.CyclicHessenberg.shift_loopColoringLLT_eq_recursiveExpansion
#print axioms VerticalStripLLT.CyclicHessenberg.recursiveCyclicExpansion_coeff_nonneg
#print axioms VerticalStripLLT.CyclicHessenberg.recursiveCyclicExpansion_isWeightedHomogeneous
#print axioms VerticalStripLLT.CyclicHessenberg.loopColoringLLT_has_natural_elementary_expansion

#print axioms VerticalStripLLT.CyclicHessenberg.CycleDisplay.deletionEquiv
#print axioms VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_eq_cycleSum
#print axioms VerticalStripLLT.CyclicHessenberg.cycleDisplayEquivPerm
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCycleSum_coeff
#print axioms VerticalStripLLT.CyclicHessenberg.matchingTransport_of_arbitrary_boundaries
#print axioms VerticalStripLLT.CyclicHessenberg.matchingOpenPathEquiv
#print axioms VerticalStripLLT.CyclicHessenberg.naturalOpenKernel_eq_openLayerPath_sum
#print axioms VerticalStripLLT.CyclicHessenberg.canonicalPathMatchingEquiv
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCanonicalCyclicExpansion_eq_matchingExpansion
#print axioms VerticalStripLLT.CyclicHessenberg.shift_loopColoringLLT_eq_cyclicExpansion
#print axioms VerticalStripLLT.CyclicHessenberg.cyclicExpansion_coeff_nonneg
#print axioms VerticalStripLLT.CyclicHessenberg.cyclicExpansion_isWeightedHomogeneous

#print axioms VerticalStripLLT.CyclicHessenberg.coloredLoopSortedEquiv
#print axioms VerticalStripLLT.CyclicHessenberg.compositionColorWordEquivStrictList
#print axioms VerticalStripLLT.CyclicHessenberg.runMonomialQuasisymmetric_eq
#print axioms VerticalStripLLT.CyclicHessenberg.loopColoringLLT_eq_sortedLoopColoringSum
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_coeff
#print axioms VerticalStripLLT.CyclicHessenberg.cyclicExpansion_coeff_eq_card_markedMatching
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_coeff_eq_zero_of_weight_ne
#print axioms VerticalStripLLT.Challenges.CyclicHessenberg.sortedLoopModel
#print axioms VerticalStripLLT.Challenges.CyclicHessenberg.positiveCycleExpansion
#print axioms VerticalStripLLT.Challenges.CyclicHessenberg.positiveMatchingExpansion
#print axioms VerticalStripLLT.Challenges.CyclicHessenberg.elementaryCoefficientFormula
#print axioms VerticalStripLLT.Challenges.CyclicHessenberg.ePositive

#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_empty_support
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_singleton_support
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_identity
#print axioms VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_pair
#print axioms VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_triple
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_completeTwo
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_completeThree
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_kimOh_example67
#print axioms VerticalStripLLT.CyclicHessenberg.specialize_shift_cyclicLLT_zero
#print axioms VerticalStripLLT.CyclicHessenberg.loopCoverMatchingEquiv
#print axioms VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_at_zero
#print axioms VerticalStripLLT.CyclicHessenberg.Examples.decreasing_color_tie
#print axioms VerticalStripLLT.CyclicHessenberg.Examples.later_reverse_event_with_tie

#print axioms VerticalStripLLT.CyclicHessenberg.Examples.reverse_tie_ascent_pos

-- Fail the build on an unexpected axiom, even when the remote log is truncated.
run_cmd do
  let declarations : List Lean.Name := [
    ``VerticalStripLLT.CyclicHessenberg.Hessenberg.ext,
    ``VerticalStripLLT.CyclicHessenberg.Hessenberg.oneBased_iff,
    ``VerticalStripLLT.CyclicHessenberg.orderFintype,
    ``VerticalStripLLT.CyclicHessenberg.ordersEquiv,
    ``VerticalStripLLT.CyclicHessenberg.isOrder_append_left_iff,
    ``VerticalStripLLT.CyclicHessenberg.isOrder_append_right_iff,
    ``VerticalStripLLT.CyclicHessenberg.isOrder_swapAdjacent,
    ``VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.prefixKernel,
    ``VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.suffixKernel,
    ``VerticalStripLLT.CyclicHessenberg.ListExchangeCompatible.minimumDifference,
    ``VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.diagonal_contextualBalance,
    ``VerticalStripLLT.CyclicHessenberg.loopColoringLLT,
    ``VerticalStripLLT.CyclicHessenberg.loopColoringLLT_empty,
    ``VerticalStripLLT.CyclicHessenberg.loopColoringLLT_zero_alphabet,
    ``VerticalStripLLT.CyclicHessenberg.colorPrecedes_of_lt,
    ``VerticalStripLLT.CyclicHessenberg.colorPrecedes_of_gt,
    ``VerticalStripLLT.CyclicHessenberg.insertionEquiv,
    ``VerticalStripLLT.CyclicHessenberg.sum_insertOrder,
    ``VerticalStripLLT.CyclicHessenberg.exchangeCompatible_iff_commute,
    ``VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.mul,
    ``VerticalStripLLT.CyclicHessenberg.ExchangeCompatible.list_prod,
    ``VerticalStripLLT.CyclicHessenberg.rootDeletion_exchangeCompatible,
    ``VerticalStripLLT.CyclicHessenberg.signedRootDeletion_eq_rootDeletion,
    ``VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_add,
    ``VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_smul,
    ``VerticalStripLLT.CyclicHessenberg.kernelExpansion_coeff_nonneg,
    ``VerticalStripLLT.CyclicHessenberg.cast_naturalOpenKernel_eq_shift_rawOpenKernel,
    ``VerticalStripLLT.CyclicHessenberg.naturalOpenKernel_entry_eq_sum,
    ``VerticalStripLLT.CyclicHessenberg.orderColoringEnumerator_empty,
    ``VerticalStripLLT.CyclicHessenberg.orderColoringEnumerator_zero_alphabet,
    ``VerticalStripLLT.CyclicHessenberg.loopBoundaryPathEquiv,
    ``VerticalStripLLT.CyclicHessenberg.sortColorOrder_unique,
    ``VerticalStripLLT.CyclicHessenberg.sortColorOrder_orderEquiv_precedes,
    ``VerticalStripLLT.CyclicHessenberg.layerAscentCount_eq_sum,
    ``VerticalStripLLT.CyclicHessenberg.laterSpectatorIndicatorSwap,
    ``VerticalStripLLT.CyclicHessenberg.contextEq_iff_all_contexts,
    ``VerticalStripLLT.CyclicHessenberg.repeated_sandwich,
    ``VerticalStripLLT.CyclicHessenberg.descendingClass_mul_inverseClass,
    ``VerticalStripLLT.CyclicHessenberg.inverseClass_mul_descendingClass,
    ``VerticalStripLLT.CyclicHessenberg.descendingClass_conjugate_ad,
    ``VerticalStripLLT.CyclicHessenberg.wordAd_terminates,
    ``VerticalStripLLT.CyclicHessenberg.descendingClass_eq_sublistSum,
    ``VerticalStripLLT.CyclicHessenberg.inverseClass_eq_sublistSum,
    ``VerticalStripLLT.CyclicHessenberg.colorClassProduct_insert_root,
    ``VerticalStripLLT.CyclicHessenberg.finite_weight_shift,
    ``VerticalStripLLT.CyclicHessenberg.layerListWeight_exchangeCompatible,
    ``VerticalStripLLT.CyclicHessenberg.layerListWeight_eq,
    ``VerticalStripLLT.CyclicHessenberg.layerKernelAt_exchangeCompatible,
    ``VerticalStripLLT.CyclicHessenberg.naturalOpenKernel_exchangeCompatible,
    ``VerticalStripLLT.CyclicHessenberg.shiftedRawOpenKernel_exchangeCompatible,
    ``VerticalStripLLT.CyclicHessenberg.list_prod_eq_sum_fixedBoundaryPath,
    ``VerticalStripLLT.CyclicHessenberg.rawOpenKernel_diagonal_eq_closedLayerPath_sum,
    ``VerticalStripLLT.CyclicHessenberg.loopEventEquiv_mem,
    ``VerticalStripLLT.CyclicHessenberg.coloredLoopAscentCount_eq_path_sum,
    ``VerticalStripLLT.CyclicHessenberg.loopColoringLLT_eq_kernelColoringLLT,
    ``VerticalStripLLT.CyclicHessenberg.colorInsertion_eq_adExpansion,
    ``VerticalStripLLT.CyclicHessenberg.wordAd_eq_signedSetMountain,
    ``VerticalStripLLT.CyclicHessenberg.mountainWordSum_eval_positive,
    ``VerticalStripLLT.CyclicHessenberg.colorInsertion_eq_mountainSum,
    ``VerticalStripLLT.CyclicHessenberg.colorClassProduct_restrict,
    ``VerticalStripLLT.CyclicHessenberg.sum_subwords_eq_sum_colorings,
    ``VerticalStripLLT.CyclicHessenberg.colorClassProduct_eq_positionProduct,
    ``VerticalStripLLT.CyclicHessenberg.colorClassProduct_eval,
    ``VerticalStripLLT.CyclicHessenberg.colorClassProduct_eval_of_subset,
    ``VerticalStripLLT.CyclicHessenberg.SupportedKernel.rootDeletion,
    ``VerticalStripLLT.CyclicHessenberg.weightedKernelColoring_insert_max,
    ``VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_eval_eq_weightedKernelColoring,
    ``VerticalStripLLT.CyclicHessenberg.xQShift_loopColoringLLT_eq_naturalOpenKernel_coloring,
    ``VerticalStripLLT.CyclicHessenberg.shift_loopColoringLLT_eq_recursiveExpansion,
    ``VerticalStripLLT.CyclicHessenberg.recursiveCyclicExpansion_coeff_nonneg,
    ``VerticalStripLLT.CyclicHessenberg.recursiveCyclicExpansion_isWeightedHomogeneous,
    ``VerticalStripLLT.CyclicHessenberg.loopColoringLLT_has_natural_elementary_expansion,
    ``VerticalStripLLT.CyclicHessenberg.CycleDisplay.deletionEquiv,
    ``VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_eq_cycleSum,
    ``VerticalStripLLT.CyclicHessenberg.cycleDisplayEquivPerm,
    ``VerticalStripLLT.CyclicHessenberg.naturalCycleSum_coeff,
    ``VerticalStripLLT.CyclicHessenberg.matchingTransport_of_arbitrary_boundaries,
    ``VerticalStripLLT.CyclicHessenberg.matchingOpenPathEquiv,
    ``VerticalStripLLT.CyclicHessenberg.naturalOpenKernel_eq_openLayerPath_sum,
    ``VerticalStripLLT.CyclicHessenberg.canonicalPathMatchingEquiv,
    ``VerticalStripLLT.CyclicHessenberg.naturalCanonicalCyclicExpansion_eq_matchingExpansion,
    ``VerticalStripLLT.CyclicHessenberg.shift_loopColoringLLT_eq_cyclicExpansion,
    ``VerticalStripLLT.CyclicHessenberg.cyclicExpansion_coeff_nonneg,
    ``VerticalStripLLT.CyclicHessenberg.cyclicExpansion_isWeightedHomogeneous,
    ``VerticalStripLLT.CyclicHessenberg.coloredLoopSortedEquiv,
    ``VerticalStripLLT.CyclicHessenberg.compositionColorWordEquivStrictList,
    ``VerticalStripLLT.CyclicHessenberg.runMonomialQuasisymmetric_eq,
    ``VerticalStripLLT.CyclicHessenberg.loopColoringLLT_eq_sortedLoopColoringSum,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_coeff,
    ``VerticalStripLLT.CyclicHessenberg.cyclicExpansion_coeff_eq_card_markedMatching,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_coeff_eq_zero_of_weight_ne,
    ``VerticalStripLLT.Challenges.CyclicHessenberg.sortedLoopModel,
    ``VerticalStripLLT.Challenges.CyclicHessenberg.positiveCycleExpansion,
    ``VerticalStripLLT.Challenges.CyclicHessenberg.positiveMatchingExpansion,
    ``VerticalStripLLT.Challenges.CyclicHessenberg.elementaryCoefficientFormula,
    ``VerticalStripLLT.Challenges.CyclicHessenberg.ePositive,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_empty_support,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_singleton_support,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_identity,
    ``VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_pair,
    ``VerticalStripLLT.CyclicHessenberg.naturalKernelExpansion_triple,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_completeTwo,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_completeThree,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_kimOh_example67,
    ``VerticalStripLLT.CyclicHessenberg.specialize_shift_cyclicLLT_zero,
    ``VerticalStripLLT.CyclicHessenberg.loopCoverMatchingEquiv,
    ``VerticalStripLLT.CyclicHessenberg.naturalCyclicExpansion_at_zero,
    ``VerticalStripLLT.CyclicHessenberg.Examples.decreasing_color_tie,
    ``VerticalStripLLT.CyclicHessenberg.Examples.later_reverse_event_with_tie,
    ``VerticalStripLLT.CyclicHessenberg.Examples.reverse_tie_ascent_pos ]
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in declarations do
    for dependency in (← Lean.collectAxioms declaration) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {declaration}"
  Lean.logInfo m!"Cyclic axiom guard passed for {declarations.length} declarations."
