package souther.compiler.observe;

import souther.compiler.diag.SourceRef;

import java.util.List;
import java.util.Optional;

/**
 * One reason a measure could not read everything it needed, as data rather than as a sentence.
 *
 * <p>An adequacy report is read by a build and by an agent as much as by a person, so what stopped a
 * measurement carries a code and the subject it is about. A free-text reason reads well once and
 * cannot be counted, filtered, or matched against the next run.
 *
 * @param code    what happened
 * @param scope   what {@link #subject} names, so that a reader does not have to work it out. Every
 *                reader of these has to know whether a reason is about one behavior or about
 *                everything in a source — and while that was a guess from the shape of a string, three
 *                readers guessed differently and each was found separately
 * @param subject what it happened to — a behavior, a source, the module, or a position in a value
 * @param at      where, when there is a source to point at; empty for something with no position of
 *                its own, such as an invariant that arrived from a module compiled elsewhere
 */
public record Incompleteness(Code code, Scope scope, String subject, Optional<SourceRef> at) {

    /** What a reason is about, and so who it counts against. */
    public enum Scope {
        /** One behavior. Only that behavior's measures are affected. */
        BEHAVIOR,
        /** One source: whatever it holds, which is exactly what could not be read. */
        SOURCE,
        /** The module, and so everything in it. */
        MODULE,
        /** A position inside a value — an axis path, a field chain. */
        POSITION;

        /** Whether this is about one behavior in particular, as against something larger holding it.
         * A reason about something larger is a reason about every behavior inside it. */
        public boolean isOneBehavior() {
            return this == BEHAVIOR;
        }
    }

    public enum Code {
        /** A value could not be read back into an observed form at all. */
        VALUE_UNREADABLE,
        /** A value was larger than the limits allow, so only its shape was kept. */
        VALUE_TRUNCATED,
        /** A row could not be decided — it spent its budget, or the evaluation did not answer — so
         * what it would have covered is unknown. */
        ROW_UNDECIDED,
        /**
         * The generated classes would not link.
         *
         * <p>Named for what is caught, which is a {@code LinkageError} and not one of the things
         * that raise it. The case this exists for is the runtime being off the host's classpath —
         * it is {@code provided}, like CTFE — and the JVM raises the same error for a class that
         * will not verify, one whose format it does not accept, and one compiled against a
         * different version of what it calls. Nothing here can tell them apart, so nothing here
         * says which.
         *
         * <p>And nothing here says what did not happen next. Three places write it: an example that
         * would not run, a fill that could not put its candidates through the decoder, and a
         * boundary that could not build one. Only the first is rows that did not run — the other
         * two happen after the rows were read — so a reader of the code alone knows the linking
         * failed and no more than that.
         */
        LINKAGE_FAILED,
        /** Nothing was observed from here, so what its rows cover is unknown. */
        OBSERVATION_ABSENT,
        /**
         * The instrumented classes could not be made, so the arms went unread.
         *
         * <p>Wider than the name. Its one producer writes it wherever the classes an arm-measuring
         * evaluation needs are absent — a backend that failed on them, inputs that were not there —
         * and a probe whose mapping was lost is one way to arrive at that rather than the whole of
         * it. The name is left alone here and read against the rest of the vocabulary at once.
         */
        PROBE_MAPPING_LOST,
        /** A search gave up before it could decide. */
        SEARCH_LIMIT
    }

    public Incompleteness {
        at = at == null ? Optional.empty() : at;
    }

    public static Incompleteness of(Code code, Scope scope, String subject) {
        return new Incompleteness(code, scope, subject, Optional.empty());
    }

    public static Incompleteness at(Code code, Scope scope, String subject, SourceRef where) {
        return new Incompleteness(code, scope, subject, Optional.ofNullable(where));
    }

    /** Whether this counts against {@code behavior} — either by naming it, or by being about
     * something larger that holds it. */
    public boolean countsAgainst(String behavior) {
        return scope.isOneBehavior() ? subject.equals(behavior) : true;
    }

    /** What makes two of these the same reason. A module's classes failing to be instrumented is one
     * fact however many sources went looking for them. */
    public Object identity() {
        return List.of(code, scope, subject);
    }
}
