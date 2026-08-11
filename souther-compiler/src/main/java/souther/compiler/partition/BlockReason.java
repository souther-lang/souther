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
 * <p>Sealed, and projected to the public vocabulary by one exhaustive switch with no
 * {@code default} ({@link #reported()}). A reason added here and not said out there stops the
 * compile rather than arriving in a report as a word chosen because it was nearest.
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

    /**
     * The word an adequacy document writes for {@code reason}.
     *
     * <p>Deliberately coarser: what a reader of the document is promised is which kind of thing
     * stopped the derivation, not which capability this compiler is missing this month. Three
     * traversals are one word out there because a reader cannot act on the difference — the model
     * is the same either way, and which of them this compiler cannot walk is this compiler's news.
     *
     * <p>In one place rather than answered per case, because a coarsening is only reviewable where
     * the collapses are visible together: what wants checking is which reasons share a word, and a
     * method on each case shows a reader one mapping at a time. No {@code default}, so a reason
     * added above stops the compile here until it has been said what a report calls it.
     */
    static UndividedPosition.Reason reported(BlockReason reason) {
        return switch (reason) {
            case TypeUnresolved _ -> UndividedPosition.Reason.TYPE_UNRESOLVED;
            case DepthLimit _ -> UndividedPosition.Reason.DEPTH_LIMIT;
            case UnsupportedTraversal _ -> UndividedPosition.Reason.UNSUPPORTED_TRAVERSAL;
        };
    }
}
