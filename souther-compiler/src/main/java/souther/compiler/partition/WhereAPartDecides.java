package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.CasesHeldTo;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

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
 * @param part    which of the author's lines this is a place of, and which place
 * @param decides the case: parts of the statement that hold together beside the line, where
 *                crossing it turns the statement round. Over the relations the statement holds,
 *                every one of them a relation over the input's own numbers — so a row's values say
 *                whether it holds
 */
public record WhereAPartDecides(PlaceOfALine part, Proposition decides) {

    public WhereAPartDecides {
        Objects.requireNonNull(part, "a line of a statement is one of its lines");
        Objects.requireNonNull(decides, "a line decides somewhere, or nowhere");
    }

    /**
     * Where the line decides, as a report says it after what a row there has to do on the
     * positions {@code readAt} — or null where that says all of it.
     *
     * <p>Said because it is part of the line. Two readings of one comparison at one place can be
     * readings of two lines in two cases, and the place and the values alone tell a reader nothing
     * about which a row of theirs is at: {@code month.value <= minimum(term)} asks for a month above
     * 12 where {@code term} is {@code OneYear} and for one above 24 where it is {@code TwoYear}.
     *
     * <p>The cases of values the line decides in, and nothing else of where it decides: which case
     * a value is, whether it holds a value, which truth it is. Those are what a row is written in
     * and what the values of the point do not say. The relations beside them are said by the
     * values a search composes against; written out here as well, a reader is shown how the
     * statement was taken apart — a part read once held and once failing where one of them is
     * enough — and not anything a row has to do.
     *
     * <p>What every row in the case is, read through the whole of it ({@link CasesHeldTo}): a case
     * said as one of several things is where each of them holds, and what they all hold a value
     * to is what the case does.
     *
     * <p>Less what the positions already say. A line at a field of one case of a value decides
     * where the value is that case, and the position it is read at is named through that case.
     */
    public String said(List<TermPath> readAt) {
        List<String> said = new ArrayList<>();
        CasesHeldTo.of(decides).forEach((at, held) -> {
            switch (held) {
                case CasesHeldTo.Held.OneOf(var cases) -> {
                    if (readAt.stream().noneMatch(each -> each.isAtOrUnder(at.refine(cases)))) {
                        said.add(at + " is " + spelled(cases));
                    }
                }
                case CasesHeldTo.Held.NoneOf(var cases) -> said.add(at + " is not "
                        + spelled(cases));
                case CasesHeldTo.Held.ATruth(var holds) -> said.add(at + " is " + holds);
            }
        });
        return said.isEmpty() ? null : String.join(" and ", said);
    }

    private static String spelled(CasesLeft cases) {
        return cases.atoms().stream().map(Refinement::spelled).collect(Collectors.joining(" or "));
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

            /** In the order the reasons were met, which is the order a reader is told them in. */
            public CouldNotTell {
                why = Collections.unmodifiableSet(new LinkedHashSet<>(why));
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

        /** Reads {@code row} the way {@link #at} does, for the walk that finds which containers a
         *  row has to choose an element of ({@link AStatementAtARow#lookAt}). */
        void lookAt(BorderQuantity.Observation row) {
            decides.lookAt(row);
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
