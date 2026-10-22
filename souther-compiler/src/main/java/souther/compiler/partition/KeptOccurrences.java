package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.List;
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
 * <p>A statement that reads nothing but positions of the input, so that which places a number of
 * the kept occurrences is read off is said in full ({@link #placesRead}). One that reads
 * something no position is — an answer, a value a body bound — is kept by nothing here
 * ({@link #of}).
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
        if (PositionsAStatementReads.of(meeting).isEmpty()) {
            throw new IllegalArgumentException("what keeps the elements of " + container
                    + " reads something no position is: " + meeting.key());
        }
    }

    /** The occurrences of {@code container}'s elements meeting {@code meeting}, or null where it
     *  reads something no position of the input is. */
    static KeptOccurrences of(DecisionSubject container, Proposition meeting,
                              AStatementAtARow perElement) {
        return PositionsAStatementReads.of(meeting).isEmpty() ? null
                : new KeptOccurrences(container, meeting, perElement);
    }

    /** The container the elements are of. */
    TermPath position() {
        return container.inputPosition();
    }

    /** Every place of the input this reads: where the elements are, and each position the
     *  statement reads. */
    public List<TermPath> placesRead() {
        List<TermPath> out = new ArrayList<>();
        out.add(position());
        PositionsAStatementReads.of(meeting).orElseThrow().forEach(out::add);
        return List.copyOf(out);
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
