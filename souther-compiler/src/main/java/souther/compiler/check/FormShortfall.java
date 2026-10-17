package souther.compiler.check;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleSite;
import souther.compiler.types.ConstructOccurrence;

/**
 * Where the arithmetic stopped on a part of a rule that no reading took in, at one position.
 *
 * <p>The other half of what stops a rule about a position's values. The reading that turns a
 * clause into a set of values says what it could not take apart ({@link RuleShortfall}); the
 * reading that turns it into numeric constraints takes in what the arithmetic reads, and where that
 * stopped it has a word of its own — a value an operation made of the position, a product of two
 * values neither of which is a constant. That word is the one a rule ordering the values is told
 * where no line came of it, and a rule singling a value out is the same arithmetic stopped at the
 * same place.
 *
 * <p>Filed only where no reading took the part in at {@link #position}. Where one did, the
 * question is answered and what the arithmetic stopped on is no account of anything.
 *
 * @param occurrence the comparison the arithmetic stopped reading, and which copy of it this is
 * @param site       where a reader goes about it, which is what the author wrote
 * @param why        what the arithmetic stopped on
 * @param position   what was left with no reading of the part
 */
record FormShortfall(ConstructOccurrence occurrence, RuleSite site,
                     BlockReason.RuleReadingStopped why, FactSubject position) {

    FormShortfall {
        if (occurrence == null || site == null || why == null || position == null) {
            throw new IllegalArgumentException(
                    "where the arithmetic stopped is about a comparison somebody wrote, and says"
                            + " what it stopped on and at which position");
        }
        if (site instanceof RuleSite.TheRuleItself) {
            throw new IllegalArgumentException(
                    "the arithmetic stops on a comparison somebody wrote, and the whole of a rule"
                            + " is where a reader is sent rather than what was read");
        }
    }
}
