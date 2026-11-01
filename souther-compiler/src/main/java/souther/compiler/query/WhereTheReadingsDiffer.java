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
 * which of them each reading is.
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
 * counted among these. A group is what shares words, and holds the lines that share them; nothing
 * is kept about a line outside the group it is told apart in.
 *
 * <p><b>Mistaken for one another</b> is when the words are shared under different points by
 * different lines. Under one point the readings that say alike are the entries of a bag a surface
 * counts ({@link BorderObligationPointAssessment.ReadingSaid}), and nothing there is mistaken for
 * anything.
 *
 * <p><b>What is given is the place of the line among those that share the words</b>, in the order
 * of where they lie and then of the line the author drew. Not a case: the relations a case is
 * made of differ between two spellings of one statement, and a relation over whole numbers has
 * two spellings of its own ({@code n > 50}, {@code n >= 51}) that nothing here can tell are one.
 * The place does not depend on the order the readings were met in or on any row, so a row added
 * to the model moves nothing here.
 *
 * <p>Held for the readings of a behavior together, because the points that share words are
 * different points: {@code = 51} as the point a line is owed a row at and as the point another
 * line of the comparison cannot be at.
 */
public final class WhereTheReadingsDiffer {

    /** Nothing said alike, which is every behavior whose lines are told apart by their words. */
    public static final WhereTheReadingsDiffer NONE = new WhereTheReadingsDiffer(Map.of());

    /** What a reader is shown of a reading of a comparison at a point. */
    private record Words(RuleRef.Comparison rule, ModelOccurrence states, String axis,
                         String asks, String said) {}

    /** Which line a reading is of: the one its author drew, and where it lies — every point it
     *  asks of a row, in one order. */
    private record Line(AuthoredLine drawn, String lies) {}

    /** What shares one set of words: the points it is said under and the lines that say it. */
    private record Sharers(Set<BorderObligationPoint> points, Set<Line> lines) {
        Sharers() {
            this(new HashSet<>(), new HashSet<>());
        }
    }

    /** The lines that share words under different points, in the order that tells them apart. */
    private final Map<Words, List<Line>> sharing;

    private WhereTheReadingsDiffer(Map<Words, List<Line>> sharing) {
        this.sharing = sharing;
    }

    /** The lines among the readings of {@code byPoint} that share their words under different
     *  points. */
    static WhereTheReadingsDiffer of(
            Map<BorderObligationPoint, ? extends Map<Reading, BorderAssessment>> byPoint,
            Map<BorderObligationPoint, ? extends Map<Reading, ReadingSeat>> seats) {
        Map<Words, Sharers> byWords = new LinkedHashMap<>();
        byPoint.forEach((owed, met) -> met.forEach((where, reading) -> {
            Words words = wordsOf(reading, seats.get(owed).get(where).asked());
            if (words != null) {
                Sharers sharers = byWords.computeIfAbsent(words, _ -> new Sharers());
                sharers.points().add(owed);
                sharers.lines().add(lineOf(reading));
            }
        }));
        Map<Words, List<Line>> sharing = new LinkedHashMap<>();
        byWords.forEach((words, sharers) -> {
            if (sharers.points().size() > 1 && sharers.lines().size() > 1) {
                List<Line> ordered = new ArrayList<>(sharers.lines());
                ordered.sort(Comparator.comparing(Line::lies)
                        .thenComparing(line -> line.drawn().which().toString()));
                sharing.put(words, List.copyOf(ordered));
            }
        });
        return sharing.isEmpty() ? NONE : new WhereTheReadingsDiffer(sharing);
    }

    /** Which of the lines sharing its words {@code reading} is of at {@code point}, or null where
     *  its words are its own. */
    String label(BorderAssessment reading, DomainPoint point) {
        Words words = wordsOf(reading, point);
        List<Line> alike = words == null ? null : sharing.get(words);
        int place = alike == null ? -1 : alike.indexOf(lineOf(reading));
        return place < 0 ? null : "line " + (place + 1) + " of " + alike.size();
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

    /** What is shown of {@code reading} at {@code point}, or null where it is a reading of no
     *  statement of several lines or asks nothing of a row there. */
    private static Words wordsOf(BorderAssessment reading, DomainPoint point) {
        if (!(reading.border().origin() instanceof LineOrigin.ComparisonOrigin read)
                || read.part().isEmpty() || reading.operator(point) == null) {
            return null;
        }
        return new Words(read.read().rule(), read.read().states(), reading.axis(),
                reading.operator(point) + " " + reading.against(point), reading.decidesWhere());
    }

    /**
     * Every one of these is equal to every other.
     *
     * <p>What this holds is worked out from the readings of the points that hold it, so two
     * accounts whose points are equal hold equal ones, and an account whose points differ is
     * already told apart by them. Compared as well, it would be compared once for each point of
     * the account — each time the whole of it — whenever an answer is checked against the one
     * before it. Not a value to be used as a key of anything on its own.
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
