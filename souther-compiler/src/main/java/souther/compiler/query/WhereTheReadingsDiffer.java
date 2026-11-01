package souther.compiler.query;

import souther.compiler.check.RuleRef;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.LineOrigin;
import souther.compiler.partition.ReadingSeat;
import souther.compiler.partition.WhereAPartDecides;
import souther.compiler.query.BorderObligationPointAssessment.Reading;
import souther.compiler.types.ModelOccurrence;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

/**
 * Which lines of one comparison a report would say in the same words under different points, and
 * what tells them apart.
 *
 * <p>A reading of a line is said by the point it asks of a row and the cases of values it decides
 * in ({@link WhereAPartDecides#said}). Two lines of one comparison can be cut at one quantity in
 * cases that differ only by a relation between numbers, and then both say {@code = 51}: a point
 * no value can stand at and a point that is owed a row read as one point. The words are kept as
 * they are for every reading that is told apart by them, since they do not depend on how the
 * statement was taken apart; only the readings that would be mistaken for one another are given
 * more.
 *
 * <p><b>Which lines.</b> A line is told by its geometry, the points it asks of a row, and not by
 * the parts the statement was taken apart into: two spellings of one statement take it apart into
 * a different number of parts, and the same line has to be the same line in both. Two lines
 * sharing words under different points are the ones mistaken for each other. Under one point the
 * readings that say alike are the entries of a bag a surface counts
 * ({@link BorderObligationPointAssessment.ReadingSaid}), and nothing there is mistaken for
 * anything.
 *
 * <p><b>What is given.</b> The case itself where every line sharing the words has a case that is
 * one relation and no two are the same relation ({@link WhereAPartDecides#asOneRelation}), and
 * otherwise the place of the line among those that share the words, in the order of their
 * geometry. A case of several parts is not said, for the reason above. The place is not the order
 * the readings were met in or the order the statement was written in.
 *
 * <p>Both come from the readings and nothing else: no row and no outcome of a search, so a row
 * added to the model moves nothing here.
 *
 * <p>Held for the readings of a behavior together, because the points that share words are
 * different points: {@code = 51} as the point a line is owed a row at and as the point another
 * line of the comparison cannot be at.
 */
public final class WhereTheReadingsDiffer {

    /** Nothing said alike, which is every behavior whose lines are told apart by their words. */
    public static final WhereTheReadingsDiffer NONE = new WhereTheReadingsDiffer(Map.of());

    /** What a report says of a reading of a comparison at a point. */
    private record Words(RuleRef.Comparison rule, ModelOccurrence states, String asks,
                         String said) {}

    /** What shares one set of words: the points it is said under and the lines that say it. */
    private record Sharers(Set<BorderObligationPoint> points, Set<String> lines) {
        Sharers() {
            this(new HashSet<>(), new TreeSet<>());
        }
    }

    /** For the words that are shared under different points, what each line sharing them is told
     *  apart by. */
    private final Map<Words, Map<String, String>> sharing;

    private WhereTheReadingsDiffer(Map<Words, Map<String, String>> sharing) {
        this.sharing = sharing;
    }

    /** The lines among the readings of {@code byPoint} that share their words under different
     *  points. */
    static WhereTheReadingsDiffer of(
            Map<BorderObligationPoint, ? extends Map<Reading, BorderAssessment>> byPoint,
            Map<BorderObligationPoint, ? extends Map<Reading, ReadingSeat>> seats) {
        Map<Words, Sharers> byWords = new LinkedHashMap<>();
        Map<String, Set<WhereAPartDecides>> partsOf = new LinkedHashMap<>();
        byPoint.forEach((owed, met) -> met.forEach((where, reading) -> {
            if (!isAReadingOfAStatement(reading)) {
                return;
            }
            Words words = wordsOf(reading, seats.get(owed).get(where).asked());
            if (words != null) {
                String line = lineOf(reading);
                Sharers sharers = byWords.computeIfAbsent(words, _ -> new Sharers());
                sharers.points().add(owed);
                sharers.lines().add(line);
                partsOf.computeIfAbsent(line, _ -> new HashSet<>()).add(partOf(reading));
            }
        }));
        Map<Words, Map<String, String>> sharing = new LinkedHashMap<>();
        byWords.forEach((words, sharers) -> {
            if (sharers.points().size() > 1 && sharers.lines().size() > 1) {
                sharing.put(words, toldApart(List.copyOf(sharers.lines()), partsOf));
            }
        });
        return sharing.isEmpty() ? NONE : new WhereTheReadingsDiffer(sharing);
    }

    /** What each of {@code lines}, in the order that tells them apart, is told apart by: its case
     *  where each is one relation and no two are the same, and otherwise its place among them. */
    private static Map<String, String> toldApart(List<String> lines,
                                                 Map<String, Set<WhereAPartDecides>> partsOf) {
        List<Optional<String>> cases = lines.stream().map(line -> {
            Set<WhereAPartDecides> parts = partsOf.get(line);
            return parts.size() == 1 ? parts.iterator().next().asOneRelation()
                    : Optional.<String>empty();
        }).toList();
        boolean byCase = cases.stream().allMatch(Optional::isPresent)
                && new HashSet<>(cases).size() == cases.size();
        Map<String, String> out = new LinkedHashMap<>();
        for (int place = 0; place < lines.size(); place++) {
            out.put(lines.get(place), byCase ? cases.get(place).orElseThrow()
                    : "case " + (place + 1) + " of " + lines.size());
        }
        return out;
    }

    /** Where {@code reading} decides at {@code point}, told apart from the lines it shares its
     *  words with — or null where there is nothing to say of it. */
    String told(BorderAssessment reading, DomainPoint point) {
        String said = reading.decidesWhere();
        Words words = wordsOf(reading, point, said);
        Map<String, String> alike = words == null ? null : sharing.get(words);
        String told = alike == null ? null : alike.get(lineOf(reading));
        if (told == null) {
            return said;
        }
        return said == null ? told : said + " and " + told;
    }

    /** The line as its geometry: every point it asks of a row, in one order. */
    private static String lineOf(BorderAssessment reading) {
        Set<String> asks = new TreeSet<>();
        for (DomainPoint point : reading.items().keySet()) {
            if (reading.operator(point) != null) {
                asks.add(reading.operator(point) + " " + reading.against(point));
            }
        }
        return String.join("\n", asks);
    }

    private static boolean isAReadingOfAStatement(BorderAssessment reading) {
        return reading.border().origin() instanceof LineOrigin.ComparisonOrigin read
                && read.part().isPresent();
    }

    private static WhereAPartDecides partOf(BorderAssessment reading) {
        return ((LineOrigin.ComparisonOrigin) reading.border().origin()).part().orElseThrow();
    }

    /** What is said of {@code reading} at {@code point}, or null where it is a reading of no
     *  statement of several lines or asks nothing of a row there. */
    private static Words wordsOf(BorderAssessment reading, DomainPoint point) {
        return isAReadingOfAStatement(reading) && reading.operator(point) != null
                ? wordsOf(reading, point, reading.decidesWhere()) : null;
    }

    /** The same, for a reading whose cases of values have been said already. */
    private static Words wordsOf(BorderAssessment reading, DomainPoint point, String said) {
        if (!isAReadingOfAStatement(reading) || reading.operator(point) == null) {
            return null;
        }
        LineOrigin.ComparisonOrigin read = (LineOrigin.ComparisonOrigin) reading.border().origin();
        return new Words(read.read().rule(), read.read().states(),
                reading.operator(point) + " " + reading.against(point), said);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof WhereTheReadingsDiffer that && sharing.equals(that.sharing);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sharing);
    }
}
