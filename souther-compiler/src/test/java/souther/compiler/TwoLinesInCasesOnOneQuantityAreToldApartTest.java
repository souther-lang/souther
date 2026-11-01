package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison read back through a callee that branches on the quantity is drawn once per arm, and
 * two lines of it that a report would say in the same words under different points are told apart
 * by their place among the lines that share the words.
 */
class TwoLinesInCasesOnOneQuantityAreToldApartTest {

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

    private static final Pattern PLACE = Pattern.compile("\\(line (\\d+) of (\\d+)\\)");

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String human(String source) {
        Compilation compilation = measured(source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String json(String source) {
        Compilation compilation = measured(source);
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> readingsOf(String human, String axis) {
        return human.lines().map(String::strip)
                .filter(line -> line.startsWith("· read as " + axis))
                .map(line -> line.replaceFirst(" — .*", "")).sorted().toList();
    }

    @Test
    void thePointNoValueCanStandAtAndThePointOwedARowAreTwoLines() {
        List<String> at51 = readingsOf(human(CLAMPED), "full/n: = 51 ");
        assertEquals(Set.of("(line 1 of 2)", "(line 2 of 2)"), at51.stream()
                .map(line -> line.substring(line.indexOf('('))).collect(Collectors.toSet()),
                at51::toString);
        String refuted = human(CLAMPED).lines().map(String::strip)
                .filter(line -> line.contains("= 51") && line.contains("no value can stand"))
                .findFirst().orElseThrow();
        String owed = at51.stream().filter(line -> !refuted.startsWith(line)).findFirst()
                .orElseThrow();
        assertFalse(refuted.contains(placeOf(owed)), refuted + " and " + owed);
    }

    private static String placeOf(String reading) {
        Matcher place = PLACE.matcher(reading);
        assertTrue(place.find(), reading);
        return place.group();
    }

    /**
     * What tells the readings apart comes from the readings and not from the rows: a row added to
     * the model moves none of the words, whichever points it answers.
     */
    @Test
    void theWordsDoNotDependOnTheRowsTheModelHolds() {
        List<String> without = readingsOf(human(CLAMPED), "full/n");
        List<String> withMore = readingsOf(human(CLAMPED.replace("    | (0) -> false\n",
                "    | (0) -> false\n    | (60) -> false\n    | (51) -> false\n")), "full/n");
        assertFalse(withMore.isEmpty());
        // A point a row answers is no longer listed; what is listed is said as it was.
        assertTrue(without.containsAll(withMore), () -> without + " and " + withMore);
    }

    /** Another comparison whose lines lie in the same places is no line of this one. */
    @Test
    void anUnrelatedComparisonInTheSamePlacesMovesNoWordOfThisOne() {
        String withOther = CLAMPED + """

                behavior other : (n: Int) -> Bool

                let other (n) = clamp(n) == 50

                example other
                    | (50) -> true
                    | (49) -> false
                    | (0) -> false
                """;
        assertEquals(readingsOf(human(CLAMPED), "full/n"),
                readingsOf(human(withOther), "full/n"));
    }

    /**
     * Two lines on different positions that ask the same value are told apart by the position the
     * report names, so neither is given a place: {@code a} is at {@code = 51} where the first arm
     * is taken and {@code b} where it is not.
     */
    @Test
    void linesOnDifferentPositionsAreNotGivenAPlace() {
        String human = human("""
                module m

                behavior pick : (a: Int, b: Int) -> Int

                let pick (a, b) = if a > 50 then 50 else b

                behavior full : (a: Int, b: Int) -> Bool

                let full (a, b) = pick(a, b) == 50

                example full
                    | (60, 0) -> true
                    | (0, 50) -> true
                    | (0, 49) -> false
                """);
        List<String> at51 = human.lines().map(String::strip)
                .filter(line -> line.startsWith("· read as full/") && line.contains(": = 51"))
                .toList();
        assertTrue(at51.stream().anyMatch(line -> line.startsWith("· read as full/a")), human);
        assertTrue(at51.stream().anyMatch(line -> line.startsWith("· read as full/b")), human);
        assertFalse(human.contains("(line "), human);
    }

    /** A comparison that is one line in one case has nothing to tell apart. */
    @Test
    void aSingleComparisonGetsNoPlace() {
        String human = human("""
                module m

                behavior big : (n: Int) -> Bool

                let big (n) = n > 50

                example big
                    | (51) -> true
                    | (50) -> false
                """);
        assertTrue(human.contains("read as big/n"), human);
        assertFalse(human.contains(" where "), human);
        assertFalse(human.contains("(line "), human);
    }

    /**
     * A line is the same number at every point it is said at: the number is of the line among the
     * lines of its comparison, and not of the words that happen to be shared at one point.
     */
    @Test
    void aLineIsTheSameNumberAtEveryPointItIsSaidAt() {
        List<String> readings = readingsOf(human(CLAMPED), "full/n");
        for (String place : List.of("(line 1 of 2)", "(line 2 of 2)")) {
            Set<String> words = readings.stream().filter(line -> line.endsWith(place))
                    .map(line -> line.replace("· read as full/n: ", "").replace(" " + place, ""))
                    .collect(Collectors.toSet());
            assertTrue(words.contains("= 51") && words.contains("in 51 < n"), place + " " + words);
        }
    }

    /** Which line is numbered first is of the lines and not of the order the walk met them in. */
    @Test
    void theNumbersDoNotDependOnTheOrderTheReadingsWereMetIn() {
        String first = human(CLAMPED);
        for (int again = 0; again < 3; again++) {
            assertEquals(first, human(CLAMPED));
        }
    }

    /** The place is for the reader of the report; the document keeps the words its schema gives. */
    @Test
    void theDocumentSaysNoPlace() {
        String json = json(CLAMPED);
        assertFalse(json.contains("line 1 of"), json);
        assertFalse(json.contains("line 2 of"), json);
    }
}
