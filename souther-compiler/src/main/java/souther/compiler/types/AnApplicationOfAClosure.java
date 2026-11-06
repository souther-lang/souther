package souther.compiler.types;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * One application of a closure, told by the calls of the model that made it: for each closure it
 * stands inside whose call is a construct of the model, that call and which of its applications
 * it is, the outermost first.
 *
 * <p>Every call on the way, and not the innermost alone. A closure inside another is applied once
 * inside each application of the one around it, and counted from nought inside each, so its first
 * application inside the outer one's first and its first inside the outer one's second are two
 * applications with one ordinal.
 *
 * <p>Only calls the model states ({@link Made#of}). A call written inside one of the language's
 * own operations is that operation's code and no call an author wrote: it is not on the way, and
 * the calls of the model around it still are. An application made by no call of the model is told
 * by none ({@link #OF_NO_CALL_WRITTEN}), and an author is told nothing of it.
 *
 * @param by each call of the model that made it, and which of that call's applications it is
 *           inside, the outermost first
 */
public record AnApplicationOfAClosure(List<Made> by) {

    /** An application no call of the model made. */
    public static final AnApplicationOfAClosure OF_NO_CALL_WRITTEN =
            new AnApplicationOfAClosure(List.of());

    public AnApplicationOfAClosure {
        by = List.copyOf(by);
    }

    /**
     * One application a call of the model makes of a closure: the call, the construct of the
     * model it is, and which of its applications it is, counting from nought in the order a run
     * makes them.
     *
     * @param call      the call, in the copy of the body it stands in: what tells two calls of a
     *                  helper apart
     * @param construct the construct of the model the call is ({@link ModelOccurrence#statedAt}),
     *                  which is how an author is sent to it
     */
    public record Made(ACallOfAnOperation call, ModelOccurrence construct, int ordinal) {

        public Made {
            Objects.requireNonNull(call, "an application is made by some call");
            Objects.requireNonNull(construct, "a call of the model is some construct of it");
            if (ordinal < 0) {
                throw new IllegalArgumentException("applications are counted from nought: "
                        + ordinal);
            }
        }

        /**
         * The {@code ordinal}th application of {@code call}, where the call is a construct of the
         * model, and nothing where it is written inside one of the language's own operations.
         *
         * <p>The one place it is decided which calls an application is told by, so that a call
         * kept here is always one a reader can be sent to.
         */
        public static Optional<Made> of(ACallOfAnOperation call, int ordinal) {
            return ModelOccurrence.statedAt(call.at())
                    .map(construct -> new Made(call, construct, ordinal));
        }
    }

    /** Whether some call of the model made it. */
    public boolean isMadeByAWrittenCall() {
        return !by.isEmpty();
    }

    /**
     * The application of the call at {@code at} on the way to this one, the calls before it
     * included: the first {@code at + 1} of {@link #by}.
     */
    public AnApplicationOfAClosure upTo(int at) {
        return new AnApplicationOfAClosure(by.subList(0, at + 1));
    }
}
