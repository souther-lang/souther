package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;

/**
 * One thing the rules say about a number's values, as the reading of them met it.
 *
 * <p>Two variants of one kind and not two kinds. A rule either says where a run of values ends and
 * the next begins or puts one value in a class of its own, and both of them are the reading of the
 * rules arriving at something to divide a position by. Held as two lists, the reading's own order
 * across them is gone and every reader that wants all of what was said has to put the lists back
 * together — which the fan-out below and the account beside it both do, and which is where a
 * position measured at one of the two came to be measured at neither (issue #1140).
 *
 * <p>So the list of these is what a reading answers with, and the two lists are read off it.
 *
 * <p><b>Not an identity, before filing.</b> One rule about a name every case of a sum spreads is
 * filed at each of those positions, and what the partition is owed is each of them. The identity of
 * a filed one is {@link #occurrence}, which is that expansion's answer and not this reading's.
 */
public sealed interface LineEvidence {

    /** The number this is about. */
    NumericTerm at();

    /** The rule that said it. */
    OriginRef by();

    /**
     * What tells one filed piece of evidence from another.
     *
     * <p>The rule and the number together, because filing takes one rule to the positions the name
     * it is written at reaches: three cases of a sum spreading one field is one rule and three
     * numbers, and the partition owes an answer at each. Keyed by the rule alone, answering at one
     * of them would close the account over all three.
     */
    default FiledOccurrence occurrence() {
        return new FiledOccurrence(by(), at());
    }

    /** Where a run of the position's values ends and the next begins. */
    record Divides(Threshold line) implements LineEvidence {

        @Override
        public NumericTerm at() {
            return line.term();
        }

        @Override
        public OriginRef by() {
            return line.origin();
        }
    }

    /**
     * A value the rules put in a class of its own.
     *
     * <p>Apart from {@link Divides} because an equality says nothing about ranges: what it
     * distinguishes is the value from every other value, and reading it as a place to cut would put
     * a distinction between the two sides into a partition the model never drew.
     */
    record Singles(GuardThresholds.Guards.Singled point) implements LineEvidence {

        @Override
        public NumericTerm at() {
            return point.term();
        }

        @Override
        public OriginRef by() {
            return point.origin();
        }
    }

    /** One filed piece of evidence, told from every other. */
    record FiledOccurrence(OriginRef by, NumericTerm at) {}
}
