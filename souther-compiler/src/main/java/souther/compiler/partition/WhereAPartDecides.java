package souther.compiler.partition;

import souther.compiler.inputs.Quantities;
import souther.compiler.meaning.Proposition;

import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * One of the lines a statement of several relations draws, read in one case of where the statement
 * turns on it.
 *
 * <p>The two together because the second is part of what the line is. {@code Int.max(a, b) <= g}
 * turns on {@code a = g} only where {@code b <= g}, so a row at that line with {@code b} above
 * {@code g} is answered the same way on both sides of it: it stands at the line and says nothing
 * about it. A reader holding the line without where it decides would take that row for one that
 * met it.
 *
 * <p>One case and not all of them. Where a line decides may be one of several things, and each is
 * somewhere a row can be composed to be; the line is read once in each, and a row meets it in any.
 *
 * @param part    which of the statement's lines this is
 * @param decides the case: parts of the statement that hold together beside the line, where
 *                crossing it turns the statement round. Over the relations the statement holds,
 *                every one of them a relation over the input's own numbers — so a row's values say
 *                whether it holds
 */
public record WhereAPartDecides(PartOfAComparison part, Proposition decides) {

    public WhereAPartDecides {
        Objects.requireNonNull(part, "a line of a statement is one of its lines");
        Objects.requireNonNull(decides, "a line decides somewhere, or nowhere");
    }

    /** Whether a row is somewhere the line decides, or what kept that from being read. */
    sealed interface AtARow {

        /** The row is somewhere the statement turns on the line. */
        record Decides() implements AtARow {}

        /** The row is somewhere the statement does not turn on the line, or holds no value one of
         *  the relations is over. */
        record DecidesNothing() implements AtARow {}

        /** A number the relations are over could not be read at the row, for these reasons. */
        record CouldNotTell(Set<ReadingGap> why) implements AtARow {

            public CouldNotTell {
                why = Set.copyOf(why);
            }
        }

        AtARow DECIDES = new Decides();

        AtARow DECIDES_NOTHING = new DecidesNothing();
    }

    /**
     * This, put to rows: each relation it is over, as the quantity a row is read at.
     *
     * @param quantities the reading of the input, which says which order each number is on
     */
    AskedOfRows askedOfRows(String behavior, Quantities quantities) {
        return new AskedOfRows(AStatementAtARow.of(decides, behavior, quantities));
    }

    /** Where a line decides, ready to be asked of rows. */
    static final class AskedOfRows {

        private final AStatementAtARow decides;

        private AskedOfRows(AStatementAtARow decides) {
            this.decides = decides;
        }

        /** Every quantity a row is read at to say whether it is somewhere the line decides. */
        List<LinearQuantity> over() {
            return decides.over();
        }

        /**
         * Whether {@code row} is somewhere the line decides, read off its own numbers.
         *
         * <p>A relation over a position the row wrote nothing at holds of no value there, so the
         * row is not somewhere it holds.
         */
        AtARow at(BorderQuantity.Observation row) {
            return switch (decides.at(row)) {
                case AStatementAtARow.Answer.Holds _ -> AtARow.DECIDES;
                case AStatementAtARow.Answer.Fails _ -> AtARow.DECIDES_NOTHING;
                case AStatementAtARow.Answer.CouldNotTell(var why) -> new AtARow.CouldNotTell(why);
            };
        }
    }
}
