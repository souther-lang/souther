package souther.compiler.partition;

/**
 * The word an adequacy document writes for a reason a derivation stopped.
 *
 * <p>Between the two vocabularies and belonging to neither. {@link BlockReason} records what this
 * compiler could not do and does not know how it is reported; {@link UndividedPosition.Reason} is
 * what a document promises its reader they can tell apart and does not know what produced it. A
 * projection owned by either would be that one reaching into the other, which is the direction the
 * split was made to stop.
 *
 * <p>So a second surface — a diagnostic that says more than the document does — is another
 * projection beside this one rather than a change to what a reason is.
 */
final class ReportedReason {

    /**
     * Deliberately coarser than what it is given. What a reader of a document is promised is which
     * kind of thing stopped the derivation, not which capability this compiler is missing this
     * month: three missing traversals are one word, because the model reads the same whichever of
     * them it was.
     *
     * <p>One switch rather than an answer on each case, because a coarsening is only reviewable
     * where the collapses are visible together. No {@code default}, so a reason added and not said
     * stops the compile rather than arriving in a report as the nearest word that already existed.
     */
    static UndividedPosition.Reason of(BlockReason reason) {
        return switch (reason) {
            case BlockReason.TypeUnresolved _ -> UndividedPosition.Reason.TYPE_UNRESOLVED;
            case BlockReason.DepthLimit _ -> UndividedPosition.Reason.DEPTH_LIMIT;
            case BlockReason.UnsupportedTraversal _ ->
                    UndividedPosition.Reason.UNSUPPORTED_TRAVERSAL;
        };
    }

    private ReportedReason() {}
}
