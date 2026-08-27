package souther.compiler.partition;

import souther.compiler.coverage.ComparisonOccurrence;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Whether a tuple of values stands at one point of a border.
 *
 * <p>One walk for every kind of line, and the one place this is asked. What a value put at the point
 * is is the quantity's to read — it is the one thing that knows what it is a quantity of — and what
 * this adds is what belongs to the rows: which reading of a row a point is tried against, and that a
 * line a fork drew is met by getting the comparison to answer as well as by writing the value.
 *
 * <p>Asked of a tuple and not of a row, so that what is already written and what a generation has
 * just composed are put the same question. Written against a row, the question could only be asked
 * of what is in the file — and the second answer somebody wrote for a candidate would be this rule
 * again, free to agree with it until one of them moved.
 *
 * <p>Nothing here concludes anything about coverage. It says what these values do at this point; who
 * may act on that, and what a point nothing was seen at means, is the caller's.
 */
public final class StandingAtAPoint {

    /**
     * What a walk over some tuples came to at one point.
     *
     * <p>Four answers because the two that are not found are not one fact. A tuple that could not be
     * read leaves the point undecided; a tuple that stands at the level and has no account of its
     * run is one nothing can say reached the comparison, which is not the same as one that ran and
     * did not reach it. Which of them a caller may treat as a miss is the caller's to say.
     */
    public enum Met { YES, NO, NOT_WATCHED, UNREADABLE }

    /**
     * The first of {@code rows} that stands there, or why none was found.
     *
     * @param site which comparison a row has to have got an answer out of, for a rule that meeting
     *             takes more than standing at the level. Empty where standing there is the whole
     *             of it
     */
    public static Met met(BorderQuantity quantity, BehaviorInputs where, List<ObservedInputs> rows,
                          Criterion criterion, Optional<ComparisonOccurrence> site) {
        boolean unreadable = false;
        boolean unwatched = false;
        for (ObservedInputs row : rows) {
            // A row has more than one value at a position inside a sequence, and standing at a point
            // is one element standing there. Asked for one value, such a row answered with none and
            // every point on such a line came back undecided — a measurement that could not look,
            // said of a row that wrote the values plainly.
            // The first reading both answers the point and says which steps the line's positions
            // take; the rest are tried under each choice those steps allow.
            Map<TermPath, Integer> held = new LinkedHashMap<>();
            OneReadingOfARow first = new OneReadingOfARow(where, row, Map.of(), held);
            boolean stands = false;
            boolean stopped = false;
            for (OneReadingOfARow reading : readings(where, row, quantity, criterion, first, held)) {
                switch (quantity.standsAt(criterion, reading)) {
                    // A reading that could not look, unless what it could not find was an element
                    // the row wrote none of — that is a row that was read and does not stand, and
                    // said of the reading it happened in rather than of the row, since another
                    // reading of the same row may reach the point.
                    case UNREADABLE -> stopped = stopped || !reading.wroteNothing();
                    case NO -> { }
                    case YES -> stands = true;
                }
                if (stands) {
                    break;
                }
            }
            if (stands) {
                if (site.isEmpty()) {
                    return Met.YES;   // writing the value is the whole of what there is to reach
                }
                switch (row.watched()) {
                    case Generator.Watched.Ran(var account) -> {
                        if (site.stream().allMatch(account::reached)) {
                            return Met.YES;
                        }
                    }
                    // It stands where the line is and nothing watched it get there. Said rather
                    // than counted as a row that did not reach the comparison: a run that reached
                    // nothing is something this found out, and a run nobody watched is not.
                    case Generator.Watched.NoAccount _ -> unwatched = true;
                }
            }
            unreadable = unreadable || stopped;
        }
        if (unreadable) {
            return Met.UNREADABLE;
        }
        return unwatched ? Met.NOT_WATCHED : Met.NO;
    }

    /**
     * One row's values under one reading of it: an element chosen at each step inside a sequence
     * the line's positions take.
     *
     * <p>A row standing at a point is one of its readings standing there, and a reading has to be
     * one: two positions under one person are that person's two values, and offering the first
     * person's age beside the second person's status would have a row stand at a point neither
     * element is at. So an element is chosen per step and every position takes the one chosen for
     * the steps it shares — the same rule a pair of classes is read by, since it is the same
     * question.
     *
     * <p>Which readings there are is not known before the quantity has asked, since which positions
     * a line is over is its to say. So the choices are collected as it asks and the reading is run
     * again under each, until one stands or they are used up.
     */
    private static final class OneReadingOfARow implements BorderQuantity.Observation {

        private final BehaviorInputs where;
        private final ObservedInputs row;
        /** The element chosen at each step, for this reading. */
        private final Map<TermPath, Integer> chosen;
        /** How many elements each step was found to have, over every reading so far. */
        private final Map<TermPath, Integer> held;
        private boolean wroteNothing;

        OneReadingOfARow(BehaviorInputs where, ObservedInputs row,
                         Map<TermPath, Integer> chosen,
                         Map<TermPath, Integer> held) {
            this.where = where;
            this.row = row;
            this.chosen = chosen;
            this.held = held;
        }

        @Override
        public ObservedValue at(TermPath path) {
            List<BehaviorInputs.Occurrence> values = where.occurrencesAt(row.inputs(), path);
            if (values == null) {
                return null;   // the walk and the type disagree, which is the quantity's to report
            }
            if (values.isEmpty()) {
                // The row wrote no element here, so nothing of it stands anywhere on this line.
                // That is a row that was read and does not reach the point, and reporting it as a
                // value nothing could read leaves the point undecided over a row that plainly
                // settles it.
                wroteNothing = true;
                return null;
            }
            for (BehaviorInputs.Occurrence each : values) {
                each.at().forEach((step, ordinal) -> held.merge(step, ordinal + 1, Math::max));
            }
            for (BehaviorInputs.Occurrence each : values) {
                if (agrees(each)) {
                    return each.value();
                }
            }
            // No value here under this reading. Not a stop: the reading names an element this
            // position does not have, and another reading is where its values are.
            return null;
        }

        /** Whether {@code each} was reached through the elements this reading chose. */
        private boolean agrees(BehaviorInputs.Occurrence each) {
            for (Map.Entry<TermPath, Integer> step : each.at().entrySet()) {
                Integer picked = chosen.get(step.getKey());
                if (picked != null && !picked.equals(step.getValue())) {
                    return false;
                }
            }
            return true;
        }

        /** Whether the row wrote nothing at some position this line is over. */
        boolean wroteNothing() {
            return wroteNothing;
        }
    }

    /**
     * The readings of one row a point is tried against.
     *
     * <p>The first is run before the rest are known: which steps the line's positions take is the
     * quantity's to say as it reads them, so it says so by being asked once. Every choice those
     * steps allow follows it.
     */
    private static List<OneReadingOfARow> readings(BehaviorInputs where, ObservedInputs row,
                                                   BorderQuantity quantity, Criterion criterion,
                                                   OneReadingOfARow first,
                                                   Map<TermPath, Integer> held) {
        quantity.standsAt(criterion, first);
        List<OneReadingOfARow> out = new ArrayList<>();
        for (Map<TermPath, Integer> choice : readingsOver(held)) {
            out.add(new OneReadingOfARow(where, row, choice, held));
        }
        return out;
    }

    /**
     * Every reading of a row over the steps {@code held} says its positions take.
     *
     * <p>One choice per step, in every combination — which is a product and not a zip, because two
     * steps a row's positions do not take together are two independent choices. Bounded, since a
     * row holding several long lists has more readings than a measure is worth.
     */
    private static List<Map<TermPath, Integer>> readingsOver(Map<TermPath, Integer> held) {
        List<Map<TermPath, Integer>> out = new ArrayList<>();
        out.add(Map.of());
        for (Map.Entry<TermPath, Integer> step : held.entrySet()) {
            List<Map<TermPath, Integer>> wider = new ArrayList<>();
            for (Map<TermPath, Integer> each : out) {
                for (int i = 0; i < step.getValue() && wider.size() < MOST_READINGS; i++) {
                    Map<TermPath, Integer> deeper = new LinkedHashMap<>(each);
                    deeper.put(step.getKey(), i);
                    wider.add(deeper);
                }
            }
            out = wider;
        }
        return out;
    }

    /** How many readings of one row a point is tried against. */
    private static final int MOST_READINGS = 256;

    private StandingAtAPoint() {}
}
