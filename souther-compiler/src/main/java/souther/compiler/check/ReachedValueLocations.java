package souther.compiler.check;

import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.types.ReachName;

/**
 * Where a report points at what a value name reaches.
 *
 * <p>Apart from what the name means, for the reason {@link DeclarationLocations} gives: resolving a
 * name settles what it reaches, and where a report can point at that is a second question asked of
 * the one answer. A report asks it only when it is about to point, so a body whose check reports
 * nothing depends on nothing's place.
 *
 * <p>Asked of what is reached and not of a declaration. A module's helper or behavior is reached
 * where it is declared, and so is most of what the library publishes — but the library also
 * publishes names that rewrite into a call of something else, and those have no declaration of
 * their own. Which of the two a name is, is the library's to say, and it is said here and not where
 * the name was resolved.
 *
 * <p>The answer is a {@link DiagnosticPlace}, so what this compilation holds no text for is
 * answered with where it came from ({@link DiagnosticPlace.Unavailable}) rather than with nothing.
 */
public interface ReachedValueLocations {

    /**
     * Where a report points at {@code reached}.
     *
     * @throws NothingIsReached where nothing is there. Two of this compiler's answers disagreeing: a
     *     reader holding the reference got it from a resolution that said something is there
     */
    DiagnosticPlace of(ReachName.Declaration reached);

    /**
     * For a reading that was handed no compilation to ask.
     *
     * <p>Such a reading types a tree the check has already accepted, and a place is asked for only
     * by a report the check would have made first. Asked here, it is the compiler disagreeing with
     * itself — which is not {@link DiagnosticPlace.Unavailable}: that one is an answer about code
     * written elsewhere, and this reading has no answer at all.
     */
    ReachedValueLocations NOT_HELD = reached -> {
        throw new IllegalStateException("where `" + reached + "` is was asked by a reading that"
                + " types only what the check accepted, and holds no place to answer");
    };

    /** Raised where a reader asks where what a name reaches is, and nothing is there. */
    final class NothingIsReached extends IllegalStateException {

        private static final long serialVersionUID = 1L;

        public NothingIsReached(ReachName.Declaration reached) {
            super("`" + reached + "` was asked where it is, and the library or module it names has"
                    + " neither a declaration nor a rewrite of that name");
        }
    }
}
