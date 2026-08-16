package souther.compiler.diag;

/**
 * The code a coordinate carrying this names is written at it.
 *
 * <p>Value equality, though {@link WrittenAt#HERE} is the only one anybody builds. What holds it is
 * a component of {@link SourcePos}, whose own equality is read by the incremental engine deciding
 * whether an answer changed, by the store deciding whether two diagnostics are one problem, and by
 * every comparison of two nodes; resting any of those on there being a single instance would be
 * resting them on a fact nothing states.
 */
final class AtItsPlace extends WrittenAt {

    @Override
    public boolean isOutOfSight() {
        return false;
    }

    @Override
    Citation cite(SourcePos at) {
        return new WrittenCitation(new SourceRef(at.sourceId(), at));
    }

    @Override
    public WrittenAt reachedBy(String name) {
        throw new NotReachedFromElsewhere(name);
    }

    /** Marked, for the reason {@code DiagnosticPlace.NotAPlace} is: a caller that got here was
     *  branching on something other than the question, and an analysis that falls open would
     *  swallow an unmarked one and report a subject as having nothing wrong with it. */
    static final class NotReachedFromElsewhere extends IllegalStateException
            implements TheCompilerDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        NotReachedFromElsewhere(String name) {
            super("code written at its place is not reached from elsewhere, so there is no name to"
                    + " reach it by: " + name);
        }
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof AtItsPlace;
    }

    @Override
    public int hashCode() {
        return AtItsPlace.class.hashCode();
    }

    @Override
    public String toString() {
        return "Here";
    }
}
