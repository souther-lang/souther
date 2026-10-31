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
 * <p>Two reasons, and a measure that is short of the row for one is not short of it for the other.
 * Told apart here because what a reader does about each differs, and because whether a run that
 * allows more would read the case differs with them: a row's text either names a case or it does
 * not, however much a run is allowed, while a row that stopped before its case was read was stopped
 * by something a run may be allowed past.
 *
 * <p>The second is not restated as a fact about the case. What stopped the row is written where it
 * stopped, once, and is what the measure went without for this row — the same fact the reading of
 * the rows and every other measure counted over the row say of it, so it is one entry among them.
 */
public sealed interface UnreadCase {

    /** Which row. */
    RowRef rowRef();

    /**
     * No case was read from the row, and nothing it stopped at says why: its values were handed
     * over and its text names no case this reads, or nothing has evaluated it. A run that allows
     * more reads it exactly as well.
     */
    record NoCaseRead(RowRef rowRef) implements UnreadCase {

        public NoCaseRead {
            Objects.requireNonNull(rowRef, "a row nobody can name cannot be sent to");
        }
    }

    /**
     * The row did not come back before its case was read.
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
     * What the measure went without for these rows.
     *
     * <p>The rows of the first reason in one fact of the measure's own, built by
     * {@code noCaseRead}; each stop of the second as the fact it already is, so that a row stopped
     * and met by several measures is one entry in what keeps a verdict open.
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
            }
        }
        if (!unnamed.isEmpty()) {
            out.add(noCaseRead.apply(unnamed));
        }
        return WeakeningSet.ofAll(out);
    }
}
