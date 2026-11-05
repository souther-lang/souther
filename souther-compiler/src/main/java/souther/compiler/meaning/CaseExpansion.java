package souther.compiler.meaning;

import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * What a reader that stopped taking a line's cases apart at their number is told of them beside
 * why it stopped: how many ways there were, and the constructs of the model that put choices into
 * the statement the line is of.
 *
 * <p>About the cases and not about the stop. Why the line was not worked out is a reason a report
 * gathers and puts together with others like it; this is a count of one case of one line, which
 * nothing puts together with another, so it is kept beside the reason and never in it.
 *
 * <p><b>The constructs are not a factoring of the count.</b> The cases are alternatives and
 * choices held together, sharing what follows from a choice, so how many ways there are is not
 * the widths of the constructs multiplied; and one construct may be met inside another. What each
 * says is that the statement chooses there, among as many as its width.
 *
 * @param line         the quantity the line is on, named the way a report names a border on it
 * @param counted      how many ways there were of choosing one of the cases
 * @param contributing the constructs of the model the statement chooses at, each once, in the
 *                     order the statement's derivation meets them
 */
public record CaseExpansion(String line, CaseCount counted, List<Contributing> contributing) {

    public CaseExpansion {
        Objects.requireNonNull(line, "cases are a line's");
        Objects.requireNonNull(counted, "cases are some number of ways");
        contributing = List.copyOf(contributing);
    }

    /** The same cases, with what the statement chooses at beside them. */
    public CaseExpansion choosingAt(List<Contributing> at) {
        return new CaseExpansion(line, counted, at);
    }

    /** Which kind of choice a construct of the model makes, as its author wrote it. */
    public enum Kind {

        /** A search of the elements of a list for the first that meets a condition. */
        FIND,

        /** A keeping of the elements of a list that meet a condition. */
        FILTER,

        /** A {@code match}, choosing an arm. */
        MATCH,

        /** An {@code if}, choosing a branch, as many times as the statement chooses at it. */
        IF,

        /** An operation of the language whose answer is one of several cases of its arguments. */
        CASES
    }

    /**
     * One construct the statement chooses at.
     *
     * @param construct the construct, in the copy of the model it was read in
     * @param kind      which kind of choice it is
     * @param width     among how many it chooses: the elements written out a search or a keeping
     *                  goes through, the arms of a {@code match}, the cases of an operation, or
     *                  how many times the statement chooses at an {@code if}
     * @param operation the operation of the language, for a choice an operation makes
     */
    public record Contributing(ModelOccurrence construct, Kind kind, int width,
                               Optional<ValueName.Stdlib> operation) {

        public Contributing {
            Objects.requireNonNull(construct, "a choice is made at some construct");
            Objects.requireNonNull(kind, "a choice is of some kind");
            Objects.requireNonNull(operation, "an operation makes it or none does");
            if (width < 1) {
                throw new IllegalArgumentException("a choice is among some: " + width);
            }
        }
    }
}
