package souther.compiler.partition;

/**
 * Why a derivation did not finish, in this compiler's own terms.
 *
 * <p>Not {@link UndividedPosition.Reason}. That one is the vocabulary an adequacy document writes,
 * which is a promise to whoever reads the document about which cases they can tell apart; this one
 * is a record of what this compiler could not do. The two are deliberately not the same set, and
 * keeping them the same type is what froze this one: a reason could not be made more precise
 * without widening a published vocabulary, so the pressure was always back towards a word coarse
 * enough to already exist.
 *
 * <p>Split apart, the two move at their own speeds. A capability gained here removes a case here
 * and need not remove a word out there, which other cases may still be reaching; and a distinction
 * worth recording here need not be a distinction the document promises.
 *
 * <p>This knows nothing about how it is reported. Which word a document writes for one of these is
 * {@link ReportedReason}'s, so a second surface may say more of the same reason without this having
 * an opinion, and so the direction stays one way: a published vocabulary does not reach back into
 * what this compiler is allowed to know.
 */
public sealed interface BlockReason {

    /**
     * The type at the position could not be interpreted: a name denoting no declaration, or a
     * declaration reachable from itself. Such a model compiles, so this is a position a report is
     * asked about and cannot be answered for.
     */
    record TypeUnresolved() implements BlockReason {}

    /** The walk stopped before reaching what is under the position. */
    record DepthLimit() implements BlockReason {}

    /**
     * The shape at the position holds values this cannot reach into, and which reaching is missing
     * is which of {@link Traversal} it is.
     *
     * <p>Held apart rather than made one word, because what would lift each is a different piece of
     * work: choosing among however many elements a sequence holds, choosing whether an optional
     * holds one, and deciding what part of a mapping a rule is even about. Reporting them alike
     * would let one of them being implemented read as all three.
     */
    record UnsupportedTraversal(Traversal traversal) implements BlockReason {}

    /**
     * A comparison naming the position is written in a form no reader here takes apart: the
     * position inside an expression the terms do not name, or a threshold written as something
     * other than a constant.
     *
     * <p>Whichever rule wrote it. An invariant's clause and a {@code guard}'s comparison are two
     * producers of one kind of evidence (spec §example-partition), and what stopped each of them is
     * the same fact about this compiler.
     */
    record UnreadComparisonForm() implements BlockReason {}

    /** A comparison naming the position is against values no line is drawn on here — the carrier,
     *  asked of the carrier. */
    record UnreadComparisonDomain() implements BlockReason {}

    /**
     * The comparison relates two positions rather than dividing one.
     *
     * <p>Nothing is missing from the carrier: both sides are ordered, and a line drawn on either
     * against a number would be read. What is missing is a class about two positions, which a
     * partition of one is not — so a line like this is settled beside the partition rather than in
     * it, and the position it names is left with no class of its own from this rule.
     */
    record ComparisonBetweenPositions() implements BlockReason {}

    /** What a derivation would have to be able to reach into. */
    enum Traversal {

        /** The elements of a {@code List} or a {@code Set} (issue #626). */
        SEQUENCE_ELEMENT,

        /** The value an {@code Option} holds when it holds one. */
        OPTIONAL_VALUE,

        /**
         * What a {@code Map} holds. One case and not two, because which of a key and a value a rule
         * would be about has not been decided — and a distinction invented here would be a promise
         * about a semantics nobody has written.
         */
        MAPPING_CONTENT
    }

}
