package souther.compiler.check;

import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.types.ReachName;

/**
 * Where a report points at what a value name reaches — or that the reading making the report holds
 * no compilation to ask.
 *
 * <p>Apart from what the name means, for the reason {@link DeclarationLocations} gives: resolving a
 * name settles what it reaches, and where a report can point at that is a second question asked of
 * the one answer. A report asks it only when it is about to point, so a body whose check reports
 * nothing depends on nothing's place.
 *
 * <p>Asked of what is reached and not of a declaration. A module's helper or behavior is reached
 * where it is declared, and so is most of what the library publishes — but the library also
 * publishes names that rewrite into a call of something else, and those have no declaration of
 * their own. Which of the two a name is, is the library's to say, and it is said where the place is
 * answered and not where the name was resolved.
 *
 * <p>Two arms, because a reading either has a compilation to ask or it does not, and a report made
 * by one that does not is still a report. The check answering for a program is always handed one,
 * so what it reports points wherever it can. A reading without one — a backend over what the check
 * accepted, a reading that types a clause or a body to find out whether it can and keeps what it
 * learns as a stop rather than a report — says what it found and points nowhere further. Asked to
 * point instead, it would have to fail, and failing there turns a reading that stops on what the
 * check refuses into one that brings the compiler down.
 */
public sealed interface ReachedValueLocations {

    /** For a reading that holds no compilation to ask. */
    ReachedValueLocations NOT_HELD = new NotHeld();

    /** Where a report points at what a name reaches, answered by a compilation. */
    record Held(Where where) implements ReachedValueLocations {

        public Held {
            if (where == null) {
                throw new IllegalArgumentException("a reading that holds places is handed where to"
                        + " ask for them");
            }
        }
    }

    /** No compilation to ask: a report points at what the name was written as and nothing more. */
    record NotHeld() implements ReachedValueLocations {}

    /** The question a compilation answers. */
    @FunctionalInterface
    interface Where {

        /**
         * Where a report points at {@code reached}.
         *
         * <p>The answer is a {@link DiagnosticPlace}, so what this compilation holds no text for is
         * answered with where it came from ({@link DiagnosticPlace.Unavailable}) rather than with
         * nothing.
         *
         * @throws NothingIsReached where nothing is there. Two of this compiler's answers
         *     disagreeing: a reader holding the reference got it from a resolution that said
         *     something is there
         */
        DiagnosticPlace of(ReachName.Declaration reached);
    }

    /** Raised where a reader asks where what a name reaches is, and nothing is there. */
    final class NothingIsReached extends IllegalStateException {

        private static final long serialVersionUID = 1L;

        public NothingIsReached(ReachName.Declaration reached) {
            super("`" + reached + "` was asked where it is, and the library or module it names has"
                    + " neither a declaration nor a rewrite of that name");
        }
    }
}
