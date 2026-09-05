package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;

/**
 * One thing the rules say about how a position's values are divided, as the reading of them met it.
 *
 * <p>Three variants of one kind and not three kinds. A rule either says where a run of values ends
 * and the next begins, or puts one value in a class of its own, or tells a set of values from the
 * rest — and all three are the reading of the rules arriving at something to divide a position by. A
 * reader wanting all of what was said about a position wants all of them, which is one list.
 *
 * <p>So the list of these is what a reading answers with, and the projections below are read off it.
 *
 * <p><b>A line is not the shape of the kind.</b> Two of these draw one, and the third does not: a
 * predicate over the strings at a position names a set, and there is no place a row stands at
 * against it, no side of a value it keeps and no neighbour on the other side. So nothing here asks
 * for a line — a reader that wants one asks the variant that has one, and a variant with nothing
 * true to say about a line cannot be made to answer with something invented.
 *
 * <p><b>Not an identity, before filing.</b> One rule about a name every case of a sum spreads is
 * filed at each of those positions, and what the partition is owed is each of them. The identity of
 * a filed one is {@link #id}, which is that expansion's answer and not this reading's.
 */
public sealed interface PartitionEvidence {

    /** The position this is about, which one position answers: evidence divides a position, and
     *  something no single place answers divides none. */
    NumericTerm.FromOnePosition at();

    /** The rule that said it, and which reading of it this is. */
    PartitionEvidenceOrigin by();

    /**
     * What tells one filed piece of evidence from another, once it has been filed.
     *
     * <p>The rule and the position together, because filing takes one rule to the positions the
     * name it is written at reaches: three cases of a sum spreading one field is one rule and three
     * positions, and the partition owes an answer at each. Keyed by the rule alone, answering at one
     * of them would close the account over all three.
     */
    default FiledEvidenceId id() {
        return new FiledEvidenceId(by(), at());
    }

    /** Where a run of the position's values ends and the next begins. */
    record Divides(Threshold line) implements PartitionEvidence {

        @Override
        public NumericTerm.FromOnePosition at() {
            return line.term();
        }

        @Override
        public LineOrigin by() {
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
    record Singles(GuardThresholds.Guards.Singled point) implements PartitionEvidence {

        @Override
        public NumericTerm.FromOnePosition at() {
            return point.term();
        }

        @Override
        public LineOrigin by() {
            return point.origin();
        }
    }

    /**
     * A set of the position's values told from the rest.
     *
     * <p>What a behavior's rule about the strings at a position does. It draws no line: the values
     * it tells apart are not a run, so there is no place they end at and nothing is on either side
     * of anything. Read as a line it would be a cut at a value the model never named, and read as a
     * single value it would be one value standing for a set.
     */
    record BySet(SetDivision division) implements PartitionEvidence {

        @Override
        public NumericTerm.FromOnePosition at() {
            return division.term();
        }

        @Override
        public PredicateOrigin by() {
            return division.origin();
        }
    }

    /** What one filed piece of evidence is called: the rule that said it and the position it was
     *  filed at. Not a count of how many times anything reached it. */
    record FiledEvidenceId(PartitionEvidenceOrigin by, NumericTerm.FromOnePosition at) {}

    /**
     * The lines among {@code evidence}, for a reader that wants only those.
     *
     * <p>Here and not at each holder of a list. Four of them wanted the same two projections and
     * each wrote its own, which is four places to answer the day a third variant is written.
     */
    static java.util.List<Threshold> linesIn(java.util.List<PartitionEvidence> evidence) {
        return evidence.stream().filter(Divides.class::isInstance)
                .map(each -> ((Divides) each).line()).toList();
    }

    /** The values singled out among {@code evidence}, likewise. */
    static java.util.List<GuardThresholds.Guards.Singled> pointsIn(
            java.util.List<PartitionEvidence> evidence) {
        return evidence.stream().filter(Singles.class::isInstance)
                .map(each -> ((Singles) each).point()).toList();
    }

    /** The sets told from the rest among {@code evidence}, likewise. */
    static java.util.List<SetDivision> divisionsIn(java.util.List<PartitionEvidence> evidence) {
        return evidence.stream().filter(BySet.class::isInstance)
                .map(each -> ((BySet) each).division()).toList();
    }
}
