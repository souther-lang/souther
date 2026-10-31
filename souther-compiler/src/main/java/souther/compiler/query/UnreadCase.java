package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RowRef;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

/**
 * A row whose case at one place of a signature was not read, and why.
 *
 * <p>Three reasons, and a measure that is short of the row for one is not short of it for another.
 * Told apart here because what a reader does about each differs, and because whether a run that
 * allows more would read the case differs with them.
 *
 * <p>Which one a row is follows from how far the row got and from what is on record about it, and
 * from nothing else:
 *
 * <table>
 *   <caption>The reason a case was not read</caption>
 *   <tr><th>values handed over</th><th>stop on record</th><th>reason</th></tr>
 *   <tr><td>no</td><td>yes</td><td>{@link Stopped}</td></tr>
 *   <tr><td>no</td><td>no</td><td>{@link Refused}</td></tr>
 *   <tr><td>yes</td><td>either</td><td>{@link NoCaseRead}, and {@link Stopped} too where
 *       a stop can still change which sets the case is in</td></tr>
 * </table>
 *
 * <p>A row's values were handed over exactly when it got as far as having its fixtures validated
 * ({@code RowOutcome}), so the first column is the row's own and no reader infers it from what is
 * missing.
 *
 * <p>The second reason is not restated as a fact about the case. What stopped the row is written
 * where it stopped, once, and is what the measure went without for this row — the same fact the
 * reading of the rows and every other measure counted over the row say of it, so it is one entry
 * among them.
 */
public sealed interface UnreadCase {

    /** Which row. */
    RowRef rowRef();

    /**
     * The row's values were handed over and what it writes names no case this reads. A run that
     * allows more reads it exactly as well, and a reader is sent to the row to write the case out.
     */
    record NoCaseRead(RowRef rowRef) implements UnreadCase {

        public NoCaseRead {
            Objects.requireNonNull(rowRef, "a row nobody can name cannot be sent to");
        }
    }

    /**
     * The row did not come back, so what it would have said was never read, or what it got to is
     * not the whole of it.
     *
     * @param why what stopped it, as written where it stopped: the figures a run would have to be
     *            allowed past are in them. Never empty
     */
    record Stopped(RowRef rowRef, List<Incompleteness.Met> why) implements UnreadCase {

        public Stopped {
            Objects.requireNonNull(rowRef, "a row nobody can name cannot be sent to");
            why = List.copyOf(why);
            if (why.isEmpty()) {
                throw new IllegalArgumentException("a row that stopped was stopped by something: "
                        + rowRef);
            }
        }
    }

    /**
     * The row was refused before its values were handed over: an input that does not build, the
     * wrong number of inputs, an expectation that cannot be built.
     *
     * <p>It is evidence of nothing, and the refusal is reported where the row is. It cannot be the
     * row that covers a case, so it leaves no case undecided and no reader to send anywhere; it is
     * counted among the rows whose case was not read, and no more.
     */
    record Refused(RowRef rowRef) implements UnreadCase {

        public Refused {
            Objects.requireNonNull(rowRef, "a row nobody can name cannot be sent to");
        }
    }

    /**
     * What the measure went without for these rows.
     *
     * <p>The rows of the first reason in one fact of the measure's own, built by
     * {@code noCaseRead}; each stop of the second as the fact it already is, so that a row stopped
     * and met by several measures is one entry in what keeps a verdict open. The third leaves
     * nothing.
     */
    static WeakeningSet weakeningOf(List<UnreadCase> rows,
                                    Function<Set<RowRef>, Weakening> noCaseRead) {
        Set<RowRef> unnamed = new LinkedHashSet<>();
        List<Weakening> out = new ArrayList<>();
        for (UnreadCase each : rows) {
            switch (each) {
                case NoCaseRead it -> unnamed.add(it.rowRef());
                case Stopped it -> it.why().forEach(
                        gap -> out.add(new Weakening.ObservationIncomplete(gap)));
                case Refused _ -> { }
            }
        }
        if (!unnamed.isEmpty()) {
            out.add(noCaseRead.apply(unnamed));
        }
        return WeakeningSet.ofAll(out);
    }
}
