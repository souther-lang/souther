package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.partition.AuthoredLine;
import souther.compiler.partition.Border;
import souther.compiler.partition.LinearQuantity;
import souther.compiler.partition.ObservedInputs;
import souther.compiler.partition.OrderedAffineBoundary;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Whether the rows show how each position weighs into the totals one comparison cuts at several
 * places.
 *
 * <p>A weight is a fault of the computation and not of one threshold: the total is computed once
 * and every threshold of its table reads it, so a position left out or weighed wrongly moves every
 * border the same way, and a row at one border shows it for all of them. What each threshold is
 * owed on its own — where it falls and on which side — is the border's ({@link BorderAssessment});
 * what is owed here is once for the comparison and once for each position (White and Cohen, IEEE
 * TSE SE-6(3), 1980).
 *
 * <p><b>The comparison and not one total.</b> A comparison read at several windows of a table's
 * input cuts a total over each window, and the same computation weighs the same positions into
 * every one of them. A position is one obligation however many of those totals it is in.
 *
 * <p><b>A row is for a position where it stands on a border of one of those totals and that
 * position alone is away from where it starts.</b> Every other position of that total is at the
 * least it can hold, so the weight of the one that moved is the only thing the row's total is made
 * of, and rows for different positions run along different axes. A row standing on a border with
 * several positions away from their least is evidence about the sum of their weights and about no
 * one of them.
 *
 * @param line      the comparison the author wrote
 * @param positions for each position of the totals it cuts a weight can be written for, whether a
 *                  row shows it
 */
public record TiltOfAFamily(AuthoredLine line, SequencedMap<NumericTerm, Standing> positions) {

    public TiltOfAFamily {
        Objects.requireNonNull(line, "a weight is a weight in what some comparison cuts");
        positions = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(positions));
    }

    /** What the rows came to for one position. */
    public sealed interface Standing {

        /** A row standing on a border of a total with this position alone away from its least. */
        record Shown() implements Standing {}

        /** No row is. */
        record NotShown() implements Standing {}
    }

    /**
     * One border of a total as the rows are put to it.
     *
     * @param border   the border, which says which total and where it is cut
     * @param standsOn whether a row is on the border, at the point a row is owed there for where
     *                 the line falls
     * @param valuesOf what each position of the total holds at a row, once for every way the row
     *                 reaches the border
     * @param least    what the declarations leave each position, which says the least it holds
     */
    public record Reading(Border border, Predicate<ObservedInputs> standsOn,
                          Function<ObservedInputs, List<Map<NumericTerm, Place>>> valuesOf,
                          SearchRegion least) {

        public Reading {
            Objects.requireNonNull(border, "a reading is of a border");
            Objects.requireNonNull(standsOn, "a row is on a border or not");
            Objects.requireNonNull(valuesOf, "a row holds a number at each position");
            Objects.requireNonNull(least, "the least a position holds is the declarations'");
        }
    }

    /**
     * What {@code rows} show of each position of the totals {@code readings} are borders of, which
     * are the borders of one comparison's totals cut at several places.
     *
     * <p>Existential over the borders and over the ways a row reaches one, the way a point met at
     * one position of a behavior is met: a row on any border, at any reading of it, shows the
     * weight of the one position that moved.
     */
    static TiltOfAFamily of(AuthoredLine line, List<Reading> readings, List<ObservedInputs> rows) {
        if (readings.isEmpty()) {
            throw new IllegalArgumentException("a comparison cuts a total somewhere");
        }
        SequencedMap<NumericTerm, Standing> out = new LinkedHashMap<>();
        for (Reading reading : readings) {
            for (NumericTerm position : weighedBy(reading)) {
                out.putIfAbsent(position, new Standing.NotShown());
            }
        }
        for (Reading reading : readings) {
            LinearQuantity total = totalOf(reading);
            Set<NumericTerm> weighed = weighedBy(reading);
            for (ObservedInputs row : rows) {
                if (!reading.standsOn().test(row)) {
                    continue;
                }
                for (Map<NumericTerm, Place> values : reading.valuesOf().apply(row)) {
                    NumericTerm moved = theOneAwayFromItsLeast(total, weighed, values,
                            reading.least());
                    if (moved != null) {
                        out.put(moved, new Standing.Shown());
                    }
                }
            }
        }
        return new TiltOfAFamily(line, out);
    }

    /** The total a reading's border cuts. */
    static LinearQuantity totalOf(Reading reading) {
        if (!(reading.border().cut().of() instanceof LinearQuantity total)) {
            throw new IllegalArgumentException("a total is a form over positions: "
                    + reading.border());
        }
        return total;
    }

    /** The positions of a reading's total a weight can be written for. */
    static Set<NumericTerm> weighedBy(Reading reading) {
        return OrderedAffineBoundary.weighedByANumber(totalOf(reading));
    }

    /** The position of the total that is away from its least where every other is at it, or null
     *  where none is or more than one is. */
    private static NumericTerm theOneAwayFromItsLeast(LinearQuantity total,
                                                      Set<NumericTerm> weighed,
                                                      Map<NumericTerm, Place> values,
                                                      SearchRegion least) {
        NumericTerm away = null;
        for (NumericTerm term : total.terms()) {
            Place held = values.get(term);
            if (held == null) {
                return null;
            }
            if (!Count.number(held).exactly().equals(leastOf(term, least))) {
                if (away != null || !weighed.contains(term)) {
                    return null;
                }
                away = term;
            }
        }
        return away;
    }

    /**
     * The least a position holds, which is where a position of the total starts from.
     *
     * <p>The declarations' own where they bound the position from below, and nought where they say
     * nothing: a position with no least is one whose weight is shown by any value away from the
     * place every other starts at, and nought is the one place that does not depend on the rows.
     */
    private static ExactRatio leastOf(NumericTerm term, SearchRegion declarations) {
        if (term instanceof NumericTerm.FromOnePosition one) {
            NumericDomain.Bounds run = declarations.wholeRunOf(one);
            if (run != null && run.min() != null && run.min().inclusive()) {
                return Count.number(run.min().at()).exactly();
            }
        }
        return ExactRatio.ZERO;
    }
}
