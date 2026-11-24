package souther.compiler.partition;

import souther.compiler.observe.Figure;

import java.util.List;

/**
 * How far the cases a line of a statement of several is read in were worked out: what this
 * compiler has shown of them, which is not a fact of the line.
 *
 * <p>The same line in the same condition is read two ways by how far that was shown. Where the
 * cases were shown to be ones the line turns the statement in, a row in them at a point of the line
 * is where it decides. Where some of their cases nobody worked out, a row in them may be in a case
 * the line turns nothing in, standing at its point on the one side that case's rows are on, and it
 * is not told to be where the line decides ({@link ReadingGap.CasesNotWorkedOut}). A case shown to
 * be one the line decides nothing in is in neither.
 *
 * <p>Held by the line read in the cases ({@link ComparisonAssessment.Several.Part}), and handed to
 * each reading made of it ({@link WhereAPartDecides}), so the two cannot say different things.
 */
public sealed interface CasesWorkedOut {

    CasesWorkedOut SHOWN = new Shown();

    /** Every case is one the line was shown to turn the statement in. */
    record Shown() implements CasesWorkedOut {}

    /**
     * Cases some of whose cases nobody worked out, and the figures that stopped them.
     *
     * @param at in {@link Figure#inOrder}; one or more
     */
    record Stopped(List<Figure> at) implements CasesWorkedOut {

        public Stopped {
            at = Figure.inOrder(at);
            if (at.isEmpty()) {
                throw new IllegalArgumentException(
                        "cases nobody worked out were stopped at some figure");
            }
        }

        /** What a row in the cases is not told: which of them it is in. */
        ReadingGap gap() {
            return new ReadingGap.CasesNotWorkedOut(at);
        }
    }
}
