package souther.compiler.query;

import souther.compiler.observe.MeasureReason;

/**
 * Why there is nothing here for a measure to be about.
 *
 * <p>Asks nothing of anybody: no row an author writes would give this measure something to measure,
 * and only editing the model would. A {@code >->} composition has no arms, a position that is not a
 * sum has no case to cover.
 *
 * <p>A separate type from {@link NotMeasuredReason} because the two ask opposite things of a reader,
 * and while they were one type told apart by a method, a measure could come back saying its arms do
 * not apply and that somebody should go and measure them.
 *
 * <p>Closed, and here for the reason {@link FailureReason} is: a sum may name its arms only where
 * they are written, and each of these is written beside the measure that has it.
 */
public sealed interface NotApplicableReason extends MeasureReason
        permits Adequacy.BranchEvidence.NoArms,
                Adequacy.SignatureEvidence.NotASum,
                BoundaryDerivation.NoRuleDrawsALine,
                BoundaryDerivation.NoSubject,
                InputCaseEvidence.NotASum,
                OutputCaseEvidence.NotASum,
                PartitionDerivation.NoSubject,
                PartitionDerivation.NothingIsDivided {}
