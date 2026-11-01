package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.AuthoredLine;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The numbers a report gives the lines of a comparison come from the lines, and the order the
 * readings were met in moves none of them.
 *
 * <p>The words of a point are held beside the points of its behavior, so the points of two walks
 * that met the readings in two orders have to say the same words: that is also what lets the held
 * words stand out of the points' equality.
 */
class TheLinesOfAComparisonAreNumberedByTheLinesAndNotByTheWalkTest {

    private static final String CLAMPED = """
            module m

            behavior clamp : (n: Int) -> Int

            let clamp (n) = if n > 50 then 50 else n

            behavior full : (n: Int) -> Bool

            let full (n) = clamp(n) == 50

            example full
                | (50) -> true
                | (49) -> false
                | (0) -> false
            """;

    /** Several arms of one comparison, and a value handed to both sides of one maximum. */
    private static final String MANY_ARMS = """
            module m

            behavior pick : (a: Int, b: Int) -> Int

            let pick (a, b) = if a > 50 then 50 else if b > 20 then 20 else b

            behavior full : (a: Int, b: Int) -> Bool

            let full (a, b) = pick(a, b) == 50

            behavior capped : (p: Int) -> Bool

            let capped (p) = Int.max(p, p) <= 50

            example capped
                | (49) -> true
                | (50) -> true
                | (51) -> false
            """;

    private static Map<String, List<BorderAssessment>> readingsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return Adequacy.readingsOf(compilation.db(), "m");
    }

    private static List<String> wordsOfEachPoint(List<BorderAssessment> readings) {
        return BorderObligationPointAssessment.across(readings, _ -> List.of()).stream()
                .map(point -> point.point() + " = " + point.readingsSaid().stream()
                        .map(said -> said.at() + ": " + said.asks()).sorted()
                        .collect(Collectors.toList()))
                .sorted().toList();
    }

    /** The readings put in the order they came, turned round, and shuffled. */
    @Test
    void theWordsOfEveryPointAreTheSameWhateverOrderTheReadingsAreMetIn() {
        for (String source : List.of(CLAMPED, MANY_ARMS)) {
            Map<String, List<BorderAssessment>> readings = readingsOf(source);
            readings.forEach((behavior, each) -> {
                List<String> met = wordsOfEachPoint(each);
                assertFalse(met.isEmpty(), behavior);
                List<BorderAssessment> turned = new ArrayList<>(each);
                Collections.reverse(turned);
                assertEquals(met, wordsOfEachPoint(turned), behavior + " turned round");
                for (long seed = 1; seed <= 5; seed++) {
                    List<BorderAssessment> shuffled = new ArrayList<>(each);
                    Collections.shuffle(shuffled, new Random(seed));
                    assertEquals(met, wordsOfEachPoint(shuffled), behavior + " shuffled " + seed);
                }
            });
        }
    }

    /** The place of a line is said where its words are shared, and the model has such a place. */
    @Test
    void theModelsUnderTestShareWordsSoTheOrderIsAskedOfSomething() {
        List<String> words = wordsOfEachPoint(readingsOf(CLAMPED).get("full"));
        assertTrue(words.stream().anyMatch(each -> each.contains("(line ")), words::toString);
    }

    /** Two lines of one comparison are never put together, and what puts one first puts the other
     *  second. */
    @Test
    void theOrderOfTheLinesOfAComparisonIsTotalAndAntisymmetric() {
        for (String source : List.of(CLAMPED, MANY_ARMS)) {
            Map<String, List<AuthoredLine>> linesOf = new LinkedHashMap<>();
            readingsOf(source).values().forEach(readings -> readings.forEach(reading -> {
                if (reading.border().origin() instanceof
                        souther.compiler.partition.LineOrigin.ComparisonOrigin comparison) {
                    linesOf.computeIfAbsent(comparison.rule().toString(), _ -> new ArrayList<>())
                            .add(reading.border().origin().authoredLine());
                }
            }));
            linesOf.forEach((comparison, lines) -> {
                List<AuthoredLine> distinct = lines.stream().distinct().toList();
                for (AuthoredLine one : distinct) {
                    for (AuthoredLine other : distinct) {
                        int order = AuthoredLine.inASteadyOrder().compare(one, other);
                        assertEquals(one.equals(other), order == 0, comparison);
                        assertEquals(Integer.signum(order),
                                -Integer.signum(AuthoredLine.inASteadyOrder().compare(other, one)),
                                comparison);
                    }
                }
                List<AuthoredLine> sorted = distinct.stream()
                        .sorted(AuthoredLine.inASteadyOrder()).toList();
                for (long seed = 1; seed <= 5; seed++) {
                    List<AuthoredLine> shuffled = new ArrayList<>(distinct);
                    Collections.shuffle(shuffled, new Random(seed));
                    assertEquals(sorted, shuffled.stream()
                            .sorted(AuthoredLine.inASteadyOrder()).toList(), comparison);
                }
                if (distinct.size() > 1) {
                    assertNotEquals(distinct.get(0), distinct.get(1), comparison);
                }
            });
        }
    }
}
