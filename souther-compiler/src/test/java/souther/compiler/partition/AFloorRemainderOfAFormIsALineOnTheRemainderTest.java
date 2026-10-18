package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceRendering;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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
     * What the form is scaled and moved by is part of the form: the remainder is of the whole
     * dividend, its moving taken by the divisor's own remainder, so a form moved by five is the
     * form moved by one and the line is at two on that remainder.
     */
    @Test
    void aScaledAndMovedFormIsTheDividend() {
        String condition = "Int.floorMod(3 * a + d + 5, 4) == 2";
        assertEquals(List.of("2"), bordersOf("a: Int, d: Int", condition));
        boolean met = false;
        for (Row row : certifiedRows("a: Int, d: Int", condition)) {
            for (String label : row.labels()) {
                if (label.endsWith(" = 2") && label.contains("floorMod")) {
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
     * A dividend moved by a number is one dividend however the moving is spelled and wherever the
     * remainder is compared — in the comparison, behind a name, with arithmetic round it — so it is
     * one line, owed the same rows.
     */
    @Test
    void aMovedDividendIsOneLineHoweverItIsSpeltOrNamed() {
        Map<String, List<List<String>>> spellings = new LinkedHashMap<>();
        spellings.put("a: Int, d: Int", List.of(
                List.of("guard Int.floorMod(d - a + 1, 7) >= 1 else No", "Ok"),
                List.of("guard Int.floorMod(d + 1 - a, 7) >= 1 else No", "Ok"),
                List.of("let w = Int.floorMod(d - a + 1, 7)", "guard w >= 1 else No", "Ok"),
                List.of("let w = Int.floorMod(d - a + 1, 7)", "guard w + 1 >= 2 else No", "Ok")));
        spellings.put("a: Int, b: Int", List.of(
                List.of("guard Int.floorMod(3 * a + b + 5, 4) == 2 else No", "Ok"),
                List.of("guard Int.floorMod(5 + b + 3 * a, 4) == 2 else No", "Ok"),
                List.of("let w = Int.floorMod(3 * a + b + 5, 4)", "guard w == 2 else No", "Ok"),
                List.of("let w = Int.floorMod(3 * a + b + 5, 4)", "guard w - 2 == 0 else No",
                        "Ok")));
        spellings.put("xs: List<Int>", List.of(
                List.of("guard Int.floorMod(List.sum(xs) + 1, 11) <= 1 else No", "Ok"),
                List.of("let r = Int.floorMod(List.sum(xs) + 1, 11)", "guard r <= 1 else No",
                        "Ok"),
                List.of("let r = Int.floorMod(List.sum(xs) + 1, 11)", "guard 2 * r <= 3 else No",
                        "Ok")));
        spellings.forEach((parameters, bodies) -> {
            List<BorderAssessment> first = linesOf(parameters, bodies.getFirst());
            assertEquals(1, bordersOf(first).size(), () -> bodies.getFirst() + ": " + first);
            assertFalse(labelsOf(first).isEmpty(), "the line is owed rows");
            // The rows each is owed, which is what one line is; where a weighed remainder puts the
            // line between two remainders is a level of the same rows.
            for (List<String> body : bodies) {
                List<BorderAssessment> lines = linesOf(parameters, body);
                assertEquals(1, bordersOf(lines).size(), body.toString());
                assertEquals(labelsOf(first), labelsOf(lines), body.toString());
            }
        });
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

    /**
     * The remainder is one number however the comparison that meets it is written — in it, behind
     * a name, or with arithmetic round it — so it is one line, owed the same rows.
     */
    @Test
    void theRemainderIsOneLineHoweverTheComparisonMeetingItIsWritten() {
        List<BorderAssessment> inline = linesOf("a: Int, d: Int",
                List.of("guard Int.floorMod(a - d, 7) >= 1 else No", "Ok"));
        assertEquals(List.of("1"), bordersOf(inline));
        assertFalse(labelsOf(inline).isEmpty(), "the line is owed rows");
        for (List<String> body : List.of(
                List.of("let w = Int.floorMod(a - d, 7)", "guard w >= 1 else No", "Ok"),
                List.of("guard Int.floorMod(a - d, 7) + 1 >= 2 else No", "Ok"),
                List.of("let w = Int.floorMod(a - d, 7)", "guard 2 * w - 2 >= 0 else No", "Ok"))) {
            List<BorderAssessment> lines = linesOf("a: Int, d: Int", body);
            assertEquals(List.of("1"), bordersOf(lines), body.toString());
            assertEquals(labelsOf(inline), labelsOf(lines), body.toString());
        }
    }

    /**
     * A remainder weighed by two against five is the remainder against the whole number below
     * half of it: the remainder is whole, so the rows owed are the rows the whole level owes.
     */
    @Test
    void aWeighedRemainderOwesTheRowsOfTheWholeLevelItComesTo() {
        List<BorderAssessment> whole = linesOf("a: Int, d: Int",
                List.of("guard Int.floorMod(a - d, 7) <= 2 else No", "Ok"));
        List<BorderAssessment> weighed = linesOf("a: Int, d: Int", List.of(
                "let w = Int.floorMod(a - d, 7)", "guard 2 * w <= 5 else No", "Ok"));
        assertFalse(labelsOf(whole).isEmpty(), "the line is owed rows");
        assertEquals(labelsOf(whole), labelsOf(weighed));
    }

    /**
     * A remainder the divisor cannot leave is a line no row is owed at or past, and a way that
     * needs it is one nothing reaches: the remainder runs to one below the divisor whatever is
     * written of it. The same in the comparison, behind a name and with arithmetic round it, and
     * the same as for the remainder of one place.
     */
    @Test
    void aRemainderPastTheDivisorIsOwedNoRowAndNothingReachesTheWayPastIt() {
        for (List<String> body : List.of(
                List.of("guard Int.floorMod(a - d, 7) >= 7 else No", "Ok"),
                List.of("let w = Int.floorMod(a - d, 7)", "guard w >= 7 else No", "Ok"),
                List.of("guard Int.floorMod(a - d, 7) - 7 >= 0 else No", "Ok"),
                List.of("guard Int.floorMod(a, 7) >= 7 else No", "Ok"))) {
            Compilation compilation = compiled("a: Int, d: Int", body, "");
            List<BorderAssessment> lines = linesOf(compilation);
            assertEquals(List.of("7"), bordersOf(lines), body.toString());
            for (BorderAssessment border : lines) {
                border.items().forEach((point, assessed) -> {
                    boolean atOrPast = point instanceof DomainPoint.AtTheLine
                            || (point instanceof DomainPoint.BesideTheLine(var side)
                                    && side == Towards.ABOVE)
                            || (point instanceof DomainPoint.InTheRegion(var side)
                                    && side == Towards.ABOVE);
                    if (atOrPast) {
                        assertInstanceOf(ItemAssessment.NotOwed.class, assessed,
                                () -> body + ": " + point + " is past what the remainder runs to");
                    }
                });
            }
            assertEquals(List.of("a_comparison_outcome_nothing_reaches"),
                    excludedBecause(compilation), body.toString());
        }
    }

    /** Why each rule of {@code f}'s decision that is excluded is, as the report writes it. */
    private static List<String> excludedBecause(Compilation compilation) {
        JsonNode rules = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0)
                .get("decision").get("obligations");
        List<String> out = new ArrayList<>();
        rules.forEach(rule -> {
            if (rule.get("requirement") != null
                    && "excluded".equals(rule.get("requirement").stringValue())) {
                out.add(rule.get("because").get(0).stringValue());
            }
        });
        return out;
    }

    /** And so is a remainder of a number that is no place of the input, given a name. */
    @Test
    void aRemainderOfASumGivenANameIsTheLineItIsWrittenInline() {
        List<BorderAssessment> inline = linesOf("xs: List<Int>",
                List.of("guard Int.floorMod(List.sum(xs), 11) <= 1 else No", "Ok"));
        List<BorderAssessment> named = linesOf("xs: List<Int>", List.of(
                "let r = Int.floorMod(List.sum(xs), 11)", "guard r <= 1 else No", "Ok"));
        assertEquals(List.of("1"), bordersOf(inline));
        assertEquals(List.of("1"), bordersOf(named));
        assertEquals(labelsOf(inline), labelsOf(named));
    }

    /**
     * The day a difference falls on, worked out once and given a name, is measured by the rows
     * that reach each of its three stretches and the two lines between them.
     */
    @Test
    void aWeekdayOfADifferenceGivenANameIsMeasuredByItsRows() {
        Compilation compilation = compiled("a: Int, b: Int", List.of(
                        "let w = Int.floorMod(b - a, 7)",
                        "if w >= 1 && w <= 5 then Ok else No"), """
                example f
                    | (0, 1) -> Ok
                    | (0, 5) -> Ok
                    | (0, 6) -> No
                    | (0, 7) -> No
                """);
        assertEquals(List.of("1", "5"), bordersOf(linesOf(compilation)));
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                AdequacyReport.of(compilation).adequacy());
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

    /**
     * A divisor a row writes is no period, so there is no remainder to draw a line on, and the
     * report says that of the divisor.
     */
    @Test
    void aDivisorARowWritesIsNamedAsSuch() {
        assertEquals(List.of(), bordersOf("e: Int, p: Int", "Int.floorMod(e + 1, p) == 0"));
        assertTrue(reasonsOf("e: Int, p: Int", "Int.floorMod(e + 1, p) == 0").stream()
                        .allMatch(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR::equals),
                reasonsOf("e: Int, p: Int", "Int.floorMod(e + 1, p) == 0").toString());
        assertFalse(reasonsOf("e: Int, p: Int", "Int.floorMod(e + 1, p) == 0").isEmpty());
    }

    /**
     * A divisor given a name is the number it was given, to the partition as to the border: the
     * remainder is a line at the same place, and nothing about it is left unread that the written
     * divisor does not leave.
     */
    @Test
    void aDivisorGivenANameIsTheNumberItWasGiven() {
        for (String dividend : List.of("a", "a - d")) {
            String written = "Int.floorMod(" + dividend + ", 7) >= 1";
            String named = "Int.floorMod(" + dividend + ", seven) >= 1";
            assertEquals(List.of("1"),
                    linesOf("let seven = 7", "a: Int, d: Int", named).stream()
                            .map(BorderAssessment::value).toList(), named);
            assertEquals(measured("", "a: Int, d: Int", written).notRead().stream()
                            .map(PartitionEvidence.NotRead::reason).distinct().toList(),
                    measured("let seven = 7", "a: Int, d: Int", named).notRead().stream()
                            .map(PartitionEvidence.NotRead::reason).distinct().toList(),
                    named + " leaves the partition what " + written + " leaves it");
        }
    }

    /** One row of a measurement: what each input was written as and what each point is for. */
    private record Row(List<String> inputs, List<String> labels) {}

    private static List<Row> certifiedRows(String parameters, String condition) {
        return certifiedRows(linesOf(parameters, condition));
    }

    private static List<Row> certifiedRows(List<BorderAssessment> lines) {
        List<Row> rows = new ArrayList<>();
        for (BorderAssessment border : lines) {
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
        return linesOf(compiled(parameters, condition));
    }

    private static List<BorderAssessment> linesOf(String prelude, String parameters,
                                                  String condition) {
        return linesOf(compiled(prelude, parameters, condition));
    }

    private static List<BorderAssessment> linesOf(Compilation compilation) {
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    private static PartitionEvidence measured(String parameters, String condition) {
        return measured("", parameters, condition);
    }

    private static PartitionEvidence measured(String prelude, String parameters,
                                              String condition) {
        Compilation compilation = compiled(prelude, parameters, condition);
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get("f");
        assertNotNull(evidence, "f was measured");
        return evidence;
    }

    private static Compilation compiled(String parameters, String condition) {
        return compiled("", parameters, condition);
    }

    private static Compilation compiled(String prelude, String parameters, String condition) {
        return compiled(prelude, parameters, List.of("guard " + condition + " else No", "Ok"), "");
    }

    /** {@code f} over {@code parameters}, its body the lines given, with the examples after it. */
    private static Compilation compiled(String parameters, List<String> body, String examples) {
        return compiled("", parameters, body, examples);
    }

    /** The same, after the declarations {@code prelude} writes. */
    private static Compilation compiled(String prelude, String parameters, List<String> body,
                                        String examples) {
        String model = """
                module demo

                data Ok
                data No

                %s

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    %s
                }
                %s
                """.formatted(prelude, parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), String.join("\n    ", body),
                examples);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static List<String> bordersOf(String parameters, String condition) {
        return linesOf(parameters, condition).stream().map(BorderAssessment::value).toList();
    }

    /** The lines of {@code f}, its body the lines given. */
    private static List<BorderAssessment> linesOf(String parameters, List<String> body) {
        return linesOf(compiled(parameters, body, ""));
    }

    private static List<String> bordersOf(List<BorderAssessment> lines) {
        return lines.stream().map(BorderAssessment::value).toList();
    }

    /** What each certified row of {@code lines} is labelled with, in order. */
    private static List<String> labelsOf(List<BorderAssessment> lines) {
        List<String> labels = new ArrayList<>();
        for (Row row : certifiedRows(lines)) {
            labels.addAll(row.labels());
        }
        return labels.stream().sorted().toList();
    }

    private static List<UndividedPosition.Reason> reasonsOf(String parameters, String condition) {
        return measured(parameters, condition).notRead().stream()
                .map(PartitionEvidence.NotRead::reason).distinct().toList();
    }
}
