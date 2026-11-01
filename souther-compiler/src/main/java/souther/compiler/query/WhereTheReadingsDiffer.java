package souther.compiler.query;

import souther.compiler.check.RuleRef;
import souther.compiler.partition.AuthoredLine;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.LineOrigin;
import souther.compiler.partition.ReadingSeat;
import souther.compiler.query.BorderObligationPointAssessment.Reading;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * Which lines of one comparison a report would say in the same words under different points, and
 * which of the comparison's lines each reading is.
 *
 * <p>A reading is said by the position it is read at, the point it asks of a row and the cases of
 * values it decides in ({@link BorderAssessment#decidesWhere}). Two lines of one comparison can
 * be cut at one quantity in cases that differ only by a relation, and then both say
 * {@code = 51}: a point no value can stand at and a point that is owed a row read as one point.
 * The words stay as they are for every reading that is told apart by them; only a reading that
 * would be mistaken for another line's is given more.
 *
 * <p><b>Three questions, kept apart.</b> Whether two readings look alike is a question about what
 * a reader is shown ({@link Words}): the comparison, the position, the point and the cases. Which
 * line a reading is of is a question about the model ({@link Line}): the line its author drew
 * ({@link AuthoredLine}) and where it lies. And which comparison a reading belongs to is part of
 * the first, so that a line of another comparison that happens to lie in the same place is never
 * counted among these.
 *
 * <p><b>Mistaken for one another</b> is when the words are shared under different points by
 * different lines. Under one point the readings that say alike are the entries of a bag a surface
 * counts ({@link BorderObligationPointAssessment.ReadingSaid}), and nothing there is mistaken for
 * anything.
 *
 * <p><b>What is given is the place of the line among the lines of its comparison</b>, once for the
 * comparison and not for the words that happen to collide: a line is the same line at every point
 * it is said at, so a reader who follows it from one point to another finds the same number. A
 * comparison is numbered only where some of its lines are mistaken for one another, and a line of
 * it is given its number only where its words are shared.
 *
 * <p>Not a case: the relations a case is made of differ between two spellings of one statement,
 * and a relation over whole numbers has two spellings of its own ({@code n > 50},
 * {@code n >= 51}) that nothing here can tell are one.
 *
 * <p><b>The order is total.</b> The lines of a comparison are put in the order of where they lie,
 * then of everything the report says of them ({@link #shownOf}), and then of the line each is
 * among the lines its author drew ({@link AuthoredLine#inASteadyOrder}). The last is what tells
 * apart two lines that lie in one place and say every word alike, which a comparison can draw: the
 * numbers are the only words that tell them apart, so which is first has to be settled by the
 * lines and not left to the order the readings were met in. None of it depends on a row.
 *
 * <p>Held for the readings of a behavior together, because the points that share words are
 * different points: {@code = 51} as the point a line is owed a row at and as the point another
 * line of the comparison cannot be at.
 */
public final class WhereTheReadingsDiffer {

    /** Nothing said alike, which is every behavior whose lines are told apart by their words. */
    public static final WhereTheReadingsDiffer NONE =
            new WhereTheReadingsDiffer(Set.of(), Map.of());

    /** Which comparison, as a reader tells one from another. */
    private record Comparison(RuleRef.Comparison rule, ModelOccurrence states) {}

    /** What a reader is shown of a reading of a comparison at a point. */
    private record Words(Comparison of, String axis, String asks, String said) {}

    /** Which line a reading is of: the one its author drew, and where it lies — every point it
     *  asks of a row, in one order. */
    private record Line(AuthoredLine drawn, String lies) {}

    /** What shares one set of words: the points it is said under and the lines that say it. */
    private record Sharers(Set<BorderObligationPoint> points, Set<Line> lines) {
        Sharers() {
            this(new HashSet<>(), new HashSet<>());
        }
    }

    /** The words that are shared under different points by different lines. */
    private final Set<Words> shared;
    /** The lines of each comparison some of whose words are shared, in the order they are
     *  numbered in. */
    private final Map<Comparison, List<Line>> numbered;

    private WhereTheReadingsDiffer(Set<Words> shared, Map<Comparison, List<Line>> numbered) {
        this.shared = shared;
        this.numbered = numbered;
    }

    /** The lines among the readings of {@code byPoint} that share their words under different
     *  points. */
    static WhereTheReadingsDiffer of(
            Map<BorderObligationPoint, ? extends Map<Reading, BorderAssessment>> byPoint,
            Map<BorderObligationPoint, ? extends Map<Reading, ReadingSeat>> seats) {
        Map<Words, Sharers> byWords = new LinkedHashMap<>();
        Map<Comparison, Map<Line, Set<String>>> linesOf = new LinkedHashMap<>();
        byPoint.forEach((owed, met) -> met.forEach((where, reading) -> {
            Words words = wordsOf(reading, seats.get(owed).get(where).asked());
            if (words == null) {
                return;
            }
            Line line = lineOf(reading);
            Sharers sharers = byWords.computeIfAbsent(words, _ -> new Sharers());
            sharers.points().add(owed);
            sharers.lines().add(line);
            linesOf.computeIfAbsent(words.of(), _ -> new LinkedHashMap<>())
                    .computeIfAbsent(line, _ -> new TreeSet<>()).addAll(shownOf(reading));
        }));
        Set<Words> shared = new HashSet<>();
        Set<Comparison> told = new HashSet<>();
        byWords.forEach((words, sharers) -> {
            if (sharers.points().size() > 1 && sharers.lines().size() > 1) {
                shared.add(words);
                told.add(words.of());
            }
        });
        if (shared.isEmpty()) {
            return NONE;
        }
        Map<Comparison, List<Line>> numbered = new LinkedHashMap<>();
        for (Comparison comparison : told) {
            Map<Line, Set<String>> lines = linesOf.get(comparison);
            List<Line> ordered = new ArrayList<>(lines.keySet());
            ordered.sort(Comparator.comparing(Line::lies)
                    .thenComparing(line -> String.join("\n", lines.get(line)))
                    .thenComparing(Line::drawn, AuthoredLine.inASteadyOrder()));
            numbered.put(comparison, List.copyOf(ordered));
        }
        return new WhereTheReadingsDiffer(shared, numbered);
    }

    /** Which of the lines of its comparison {@code reading} is of, where its words at
     *  {@code point} are shared with another line's — or null where they are its own. */
    String label(BorderAssessment reading, DomainPoint point) {
        Words words = wordsOf(reading, point);
        if (words == null || !shared.contains(words)) {
            return null;
        }
        List<Line> lines = numbered.get(words.of());
        int place = lines.indexOf(lineOf(reading));
        return place < 0 ? null : "line " + (place + 1) + " of " + lines.size();
    }

    private static Line lineOf(BorderAssessment reading) {
        Set<String> asks = new TreeSet<>();
        for (DomainPoint point : reading.items().keySet()) {
            if (reading.operator(point) != null) {
                asks.add(reading.operator(point) + " " + reading.against(point));
            }
        }
        return new Line(reading.border().origin().authoredLine(), String.join("\n", asks));
    }

    /** Everything a reader is shown of {@code reading}, at each point it asks of a row. */
    private static Set<String> shownOf(BorderAssessment reading) {
        Set<String> shown = new TreeSet<>();
        for (DomainPoint point : reading.items().keySet()) {
            Words words = wordsOf(reading, point);
            if (words != null) {
                shown.add(words.axis() + "|" + words.asks() + "|" + words.said());
            }
        }
        return shown;
    }

    /** What is shown of {@code reading} at {@code point}, or null where it is a reading of no
     *  statement of several lines or asks nothing of a row there. */
    private static Words wordsOf(BorderAssessment reading, DomainPoint point) {
        if (!(reading.border().origin() instanceof LineOrigin.ComparisonOrigin read)
                || read.part().isEmpty() || reading.operator(point) == null) {
            return null;
        }
        return new Words(new Comparison(read.read().rule(), read.read().states()),
                reading.axis(), reading.operator(point) + " " + reading.against(point),
                reading.decidesWhere());
    }

    /**
     * Every one of these is equal to every other.
     *
     * <p>What this holds is worked out from the readings of every point of the account that holds
     * it, so two accounts whose points are equal hold equal ones, and an account that gained or
     * lost a point is already told apart by the points. That is the only way these are compared:
     * as part of the points of an account, checked against the account before it. Compared in
     * full, the whole of it would be compared once for each point of the account.
     *
     * <p>Held to that by a test that puts the readings of a behavior in other orders and asks the
     * same words of every point ({@code TheLinesOfAComparisonAreNumberedByTheLinesAndNotByTheWalkTest}).
     * Not a value to be used as a key of anything on its own, and not to be compared for a single
     * point taken out of its account.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof WhereTheReadingsDiffer;
    }

    @Override
    public int hashCode() {
        return WhereTheReadingsDiffer.class.hashCode();
    }
}
