package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a division by a written number leaves of a form of the input's numbers is a number of its
 * own, and a rule about it is a line on that number.
 *
 * <p>{@code Int.floorMod(a - d, 7) >= 1} is no line on {@code a} or on {@code d}: the pairs it
 * holds of come round at every seventh of their difference. The remainder runs from nought to six
 * whatever the pair is, so the line is drawn there, and a row is a pair whose difference leaves the
 * remainder the line is owed a row at.
 */
class AFloorRemainderOfAFormIsALineOnTheRemainderTest {

    /** A row is what the label says it is: the form its values make leaves the remainder. */
    @Test
    void aRowAtARemainderIsAPairWhoseDifferenceLeavesIt() {
        String condition = "Int.floorMod(a - d, 7) >= 1";
        assertEquals(List.of("1"), bordersOf("a: Int, d: Int", condition));

        List<String> labels = new ArrayList<>();
        for (Row row : certifiedRows("a: Int, d: Int", condition)) {
            for (String label : row.labels()) {
                if (label.startsWith("Int.floorMod(a - d, 7) = ")) {
                    long remainder = Long.parseLong(label.substring(label.lastIndexOf(' ') + 1));
                    long a = Long.parseLong(row.inputs().get(0));
                    long d = Long.parseLong(row.inputs().get(1));
                    assertEquals(remainder, Math.floorMod(a - d, 7L), label + " at " + row.inputs());
                    labels.add(label);
                }
            }
        }
        assertEquals(List.of("Int.floorMod(a - d, 7) = 0", "Int.floorMod(a - d, 7) = 1"),
                labels.stream().sorted().toList(),
                "the line is owed a row at it and one at the remainder below it");
    }

    /** The regions either side of the line are owed rows whose remainder is inside them. */
    @Test
    void aRegionIsOwedAPairWhoseRemainderIsInsideIt() {
        for (Row row : certifiedRows("a: Int, d: Int", "Int.floorMod(a - d, 7) >= 1")) {
            for (String label : row.labels()) {
                if (label.equals("1 < Int.floorMod(a - d, 7) <= 6")) {
                    long a = Long.parseLong(row.inputs().get(0));
                    long d = Long.parseLong(row.inputs().get(1));
                    long remainder = Math.floorMod(a - d, 7L);
                    assertTrue(remainder > 1 && remainder <= 6, row.inputs().toString());
                }
            }
        }
    }

    /** A number that is no place of the input — how many a list holds — is a dividend too. */
    @Test
    void theLengthOfAListIsADividendToo() {
        String condition = "Int.floorMod(List.length(xs), 11) == 3";
        assertEquals(List.of("3"), bordersOf("xs: List<Int>", condition));

        boolean met = false;
        for (Row row : certifiedRows("xs: List<Int>", condition)) {
            if (row.labels().contains("Int.floorMod(List.length(xs), 11) = 3")) {
                String list = row.inputs().getFirst();
                long length = list.equals("[]") ? 0 : list.split(",").length;
                assertEquals(3, Math.floorMod(length, 11L), list);
                met = true;
            }
        }
        assertTrue(met, "the line itself is owed a row");
    }

    /**
     * What the form is scaled by is part of the form, and what it is moved by moves the remainder:
     * a form moved by five leaves two by four exactly where the form itself leaves one, so the line
     * is on the remainder of the form and at one.
     */
    @Test
    void aScaledAndMovedFormIsTheDividend() {
        String condition = "Int.floorMod(3 * a + d + 5, 4) == 2";
        assertEquals(List.of("1"), bordersOf("a: Int, d: Int", condition));
        boolean met = false;
        for (Row row : certifiedRows("a: Int, d: Int", condition)) {
            for (String label : row.labels()) {
                if (label.endsWith(" = 1") && label.contains("floorMod")) {
                    long a = Long.parseLong(row.inputs().get(0));
                    long d = Long.parseLong(row.inputs().get(1));
                    assertEquals(2, Math.floorMod(3 * a + d + 5, 4L), row.inputs().toString());
                    met = true;
                }
            }
        }
        assertTrue(met, "the line itself is owed a row");
    }

    /**
     * A remainder the form's own values never leave is out of reach whatever the rules say, and no
     * row is written at it: twice a number and four times another are even, and an even number
     * leaves nought or two by four.
     */
    @Test
    void aRemainderTheFormNeverLeavesIsWrittenNoRow() {
        String condition = "Int.floorMod(2 * a + 4 * d, 4) == 1";
        for (Row row : certifiedRows("a: Int, d: Int", condition)) {
            for (String label : row.labels()) {
                if (label.endsWith(" = 1") && label.contains("floorMod")) {
                    throw new AssertionError("a row at a remainder the form never leaves: " + row);
                }
            }
        }
    }

    /** The days between two dates are a form of the two, so their remainder by a week is a line. */
    @Test
    void theDaysBetweenTwoDatesLeaveARemainderByAWeek() {
        String condition = "Int.floorMod(Date.daysBetween(c, d), 7) == 3";
        assertEquals(List.of("3"), bordersOf("c: Date, d: Date", condition));
        boolean met = false;
        for (Row row : certifiedRows("c: Date, d: Date", condition)) {
            if (row.labels().stream().anyMatch(label -> label.endsWith(" = 3"))) {
                long between = ChronoUnit.DAYS.between(
                        LocalDate.parse(dateOf(row.inputs().get(0))),
                        LocalDate.parse(dateOf(row.inputs().get(1))));
                assertEquals(3, Math.floorMod(between, 7L), row.inputs().toString());
                met = true;
            }
        }
        assertTrue(met, "the line itself is owed a row");
    }

    /** A date written as a fixture is {@code Date("2026-01-01")}; this is what is inside. */
    private static String dateOf(String written) {
        return written.replaceAll(".*(\\d{4}-\\d{2}-\\d{2}).*", "$1");
    }

    /**
     * A row is a pair whose difference the run computes, and a difference the run cannot compute
     * is no witness whatever it comes to as mathematics.
     *
     * <p>Every pair this guard lets through has a difference above the greatest {@code Int}, so the
     * subtraction aborts before the remainder is asked and no row reaches the line.
     */
    @Test
    void aDifferenceTheRunCannotComputeIsNoWitness() {
        String condition = "a >= 9223372036854775000 && d <= -1000"
                + " && Int.floorMod(a - d, 7) == 3";
        for (Row row : certifiedRows("a: Int, d: Int", condition)) {
            if (row.labels().stream().anyMatch(label -> label.contains("floorMod(a - d, 7)"))) {
                long a = Long.parseLong(row.inputs().get(0));
                long d = Long.parseLong(row.inputs().get(1));
                Math.subtractExact(a, d);
            }
        }
    }

    /** A remainder the divisor cannot leave settles the comparison and draws no line. */
    @Test
    void aRemainderPastTheDivisorDrawsNoLine() {
        assertEquals(List.of(), bordersOf("a: Int, d: Int", "Int.floorMod(a - d, 7) >= 7"));
    }

    /**
     * A divisor a row writes is no period, so there is no remainder to draw a line on, and the
     * report says that of the divisor.
     */
    @Test
    void aDivisorARowWritesIsNamedAsSuch() {
        assertEquals(List.of(), bordersOf("e: Int, p: Int", "Int.floorMod(e, p) == 0"));
        assertTrue(reasonsOf("e: Int, p: Int", "Int.floorMod(e, p) == 0").stream()
                        .allMatch(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR::equals),
                reasonsOf("e: Int, p: Int", "Int.floorMod(e, p) == 0").toString());
        assertFalse(reasonsOf("e: Int, p: Int", "Int.floorMod(e, p) == 0").isEmpty());
    }

    /** One row of a measurement: what each input was written as and what each point is for. */
    private record Row(List<String> inputs, List<String> labels) {}

    private static List<Row> certifiedRows(String parameters, String condition) {
        List<Row> rows = new ArrayList<>();
        for (BorderAssessment border : linesOf(parameters, condition)) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        List<String> labels = new ArrayList<>();
                        certified.row().purposes().forEach(each -> labels.addAll(each.labels()));
                        rows.add(new Row(certified.row().inputs().stream()
                                .map(each -> each.text()).toList(), labels));
                    }
                }
            }
        }
        return rows;
    }

    private static List<BorderAssessment> linesOf(String parameters, String condition) {
        Compilation compilation = compiled(parameters, condition);
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    private static PartitionEvidence measured(String parameters, String condition) {
        Compilation compilation = compiled(parameters, condition);
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get("f");
        assertNotNull(evidence, "f was measured");
        return evidence;
    }

    private static Compilation compiled(String parameters, String condition) {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    guard %s else No
                    Ok
                }
                """.formatted(parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static List<String> bordersOf(String parameters, String condition) {
        return linesOf(parameters, condition).stream().map(BorderAssessment::value).toList();
    }

    private static List<UndividedPosition.Reason> reasonsOf(String parameters, String condition) {
        return measured(parameters, condition).notRead().stream()
                .map(PartitionEvidence.NotRead::reason).distinct().toList();
    }
}
