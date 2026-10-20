package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;

import java.util.Objects;

/**
 * The occurrences of the elements of a container that meet a statement, which is what a list
 * made by an operation that kept some of them holds.
 *
 * <p>The statement is the one a count of the elements meeting it is of
 * ({@link CountedElements}), about an element of the container and nothing else: whether an
 * occurrence is counted turns on that occurrence alone, so the same value kept at one occurrence
 * and dropped at another is counted where it is kept.
 *
 * @param container  where the elements are
 * @param meeting    what an element is kept for meeting
 * @param perElement {@code meeting} put to rows, which is what an element is asked
 */
public record KeptOccurrences(DecisionSubject container, Proposition meeting,
                              AStatementAtARow perElement) {

    public KeptOccurrences {
        Objects.requireNonNull(container, "kept among the elements of a container");
        Objects.requireNonNull(meeting, "by a statement about an element");
        Objects.requireNonNull(perElement, "put to rows as an element is");
    }

    /** The container the elements are of. */
    TermPath position() {
        return container.inputPosition();
    }

    /** What this selects, spelled for a reader and for a coordinate; no identity. The position is
     *  spelled with its narrowings, as a report spells a position, and the statement by its own
     *  key, which is what holds two statements apart. */
    public String key() {
        return container.inputPosition().discriminated() + " meeting " + meeting.key();
    }

    /** Two of these are one where they keep the elements of the same container by the same
     *  statement; how the statement is put to rows is the statement's own. */
    @Override
    public boolean equals(Object other) {
        return other instanceof KeptOccurrences that && container.equals(that.container)
                && meeting.equals(that.meeting);
    }

    @Override
    public int hashCode() {
        return Objects.hash(container, meeting);
    }
}
