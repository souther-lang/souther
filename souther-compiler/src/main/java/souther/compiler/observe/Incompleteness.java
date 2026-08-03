package souther.compiler.observe;

import souther.compiler.diag.SourceRef;

import java.util.Optional;

/**
 * One reason a measure could not read everything it needed, as data rather than as a sentence.
 *
 * <p>An adequacy report is read by a build and by an agent as much as by a person, so what stopped a
 * measurement carries a code and the subject it is about. A free-text reason reads well once and
 * cannot be counted, filtered, or matched against the next run.
 *
 * @param code    what happened
 * @param subject what it happened to — a row's target, an axis path, a value's field chain
 * @param at      where, when there is a source to point at; empty for something with no position of
 *                its own, such as an invariant that arrived from a module compiled elsewhere
 */
public record Incompleteness(Code code, String subject, Optional<SourceRef> at) {

    public enum Code {
        /** A value could not be read back into an observed form at all. */
        VALUE_UNREADABLE,
        /** A value was larger than the limits allow, so only its shape was kept. */
        VALUE_TRUNCATED,
        /** A row did not finish within its time budget, so what it would have covered is unknown. */
        ROW_TIMED_OUT,
        /** The runtime is not on this host's classpath, so no row could run. */
        RUNTIME_ABSENT,
        /** A branch probe could not be tied back to the node it belongs to. */
        PROBE_MAPPING_LOST,
        /** A search gave up before it could decide. */
        SEARCH_LIMIT,
        /** An axis was dropped because the axis limit was reached. */
        AXIS_OMITTED
    }

    public Incompleteness {
        at = at == null ? Optional.empty() : at;
    }

    public static Incompleteness of(Code code, String subject) {
        return new Incompleteness(code, subject, Optional.empty());
    }

    public static Incompleteness at(Code code, String subject, SourceRef where) {
        return new Incompleteness(code, subject, Optional.ofNullable(where));
    }

    /**
     * Whether this is about one of {@code behaviors}, as against about the module or a source whole.
     *
     * <p>{@link #subject} carries a behavior name, a source id, an axis path or a field chain in one
     * string, and which of those it is has to be worked out from what else is known. What is known
     * wherever this is asked is the names the module declares — so a subject that is none of them
     * names something larger, and a reason about something larger is a reason about every behavior
     * inside it. Asked in one place so that two readers cannot answer it differently.
     */
    public boolean isAboutOneOf(java.util.Set<String> behaviors) {
        return behaviors.contains(subject);
    }
}
