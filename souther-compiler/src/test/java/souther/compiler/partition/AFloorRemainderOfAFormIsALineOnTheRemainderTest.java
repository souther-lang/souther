package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceRendering;
import souther.compiler.numeric.Towards;
import souther.compiler.query.About;
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
import java.util.function.BiPredicate;

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

    /**
     * A remainder against another number of the input is read as a line on the two added, and the
     * comparison is no longer one nothing read. However it is written, the weighed remainder and
     * number are one quantity and so one line.
     */
    @Test
    void aRemainderAgainstAnotherNumberIsALineOnTheTwo() {
        String parameters = "a: Int, b: Int, c: Int";
        Compilation compilation = compiled(parameters, "c == Int.floorMod(a + b, 11)");
        // The remainder takes every value from nought to ten with either of the numbers moved, so
        // neither is divided by it; and the number beside it is divided, by the lines at the ends
        // outside which the relation never holds.
        assertEquals(List.of("-1", "11", "0"), bordersOf(linesOf(compilation)));
        assertEquals(List.of(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                        UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                reasonsEach("a: Int, b: Int, c: Int", "c == Int.floorMod(a + b, 11)"));
        // Read, and no longer reported as written in a form nothing reads or as about a value made
        // from the position.
        assertEquals(List.of(), compilation.db().ask(new Adequacy.Coverage("demo")).value()
                .get("f").notRead().stream()
                .map(PartitionEvidence.NotRead::reason)
                .filter(reason -> reason == UndividedPosition.Reason.UNSUPPORTED_SYNTAX
                        || reason == UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE)
                .toList());
        for (String spelled : List.of("Int.floorMod(a + b, 11) == c",
                "2 * c == 2 * Int.floorMod(a + b, 11)")) {
            assertEquals(List.of("-1", "11", "0"), bordersOf(parameters, spelled), spelled);
        }
    }

    /**
     * A remainder that cannot take every value is not said to be left undivided by the number
     * beside it: {@code 2 * a + 2 * b} leaves only even remainders by 4, so which values of
     * {@code a} reach a given one is a question the relation does answer.
     */
    @Test
    void aRemainderTheFormCannotTakeEveryValueOfIsNotSaidToLeaveItsNumbersUndivided() {
        assertEquals(List.of(), reasonsEach("a: Int, b: Int, c: Int",
                "c == Int.floorMod(2 * a + 2 * b, 4)").stream()
                .filter(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES::equals).toList());
    }

    /**
     * A number the form is moved by that is read off the same place moves with it, so the place is
     * not taken through every remainder by being moved: {@code x + Int.floorMod(x, 3)} is a
     * function of {@code x}, which stays divided by the relation however the weight of {@code x}
     * leaves the remainders.
     */
    @Test
    void aNumberReadOffTheSamePlaceIsNotWhatTakesTheFormThroughEveryRemainder() {
        assertEquals(List.of(), reasonsEach("x: Int, c: Int",
                "c == Int.floorMod(x + Int.floorMod(x, 3), 4)").stream()
                .filter(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES::equals).toList());
    }

    /**
     * A check digit held against a remainder that a branch moves — the digit against nought where
     * the remainder is one at most, and against eleven less the remainder past it — is read
     * through to the end: the line on the digit and the remainder added to it are drawn, no
     * comparison of it is left as unread or as several lines held together, and a row at a line is
     * what its label says. Past the branch the remainder is two at least, so the digit is nine at
     * most there and the line beyond it is at ten.
     */
    @Test
    void aCheckDigitAgainstABranchOnTheRemainderIsReadThroughToTheEnd() {
        Compilation compilation = compiled("a: Int, b: Int, c: Int", List.of(
                "let r = Int.floorMod(a + b, 11)",
                "guard c == (if r <= 1 then 0 else 11 - r) else No", "Ok"), "");

        assertTrue(bordersOf(linesOf(compilation)).containsAll(List.of("0", "10", "11")),
                bordersOf(linesOf(compilation)).toString());
        assertFalse(bordersOf(linesOf(compilation)).contains("12"),
                () -> "no digit past the branch is eleven or ten: "
                        + bordersOf(linesOf(compilation)));
        List<UndividedPosition.Reason> unread = compilation.db()
                .ask(new Adequacy.Coverage("demo")).value().get("f").notRead().stream()
                .map(PartitionEvidence.NotRead::reason).toList();
        assertEquals(List.of(), unread.stream().filter(reason -> reason
                == UndividedPosition.Reason.UNSUPPORTED_SYNTAX
                || reason == UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE
                || reason == UndividedPosition.Reason.SEVERAL_LINES_IN_ONE_RULE).toList());
        int ofTheDigit = 0;
        int ofTheRemainder = 0;
        for (Row row : certifiedRows(linesOf(compilation))) {
            long a = Long.parseLong(row.inputs().get(0));
            long b = Long.parseLong(row.inputs().get(1));
            long c = Long.parseLong(row.inputs().get(2));
            for (String label : row.labels()) {
                if (label.startsWith("c = ")) {
                    assertEquals(c, Long.parseLong(label.substring("c = ".length())), label);
                    ofTheDigit++;
                } else if (label.startsWith("Int.floorMod(a + b, 11) = ")) {
                    assertEquals(Math.floorMod(a + b, 11L), Long.parseLong(
                            label.substring(label.lastIndexOf(' ') + 1)), label);
                    ofTheRemainder++;
                }
            }
        }
        // The loop above checks the rows there are; that there are some of each is checked here.
        assertTrue(ofTheDigit > 0 && ofTheRemainder > 0,
                ofTheDigit + " rows at the digit, " + ofTheRemainder + " at the remainder");
    }

    /**
     * A remainder is taken to leave every value only where the form is computed at the values that
     * leave them: the run stops where {@code Int} arithmetic overflows, and it does at every
     * {@code x} but three for {@code 9223372036854775807 * x}. So the number beside the
     * remainder is not said to be left either way at the values between nought and ten, and no
     * line is drawn at its ends on that account.
     */
    @Test
    void aFormTheRunCannotComputeAtTheValuesThatLeaveEveryRemainderIsNotSaidToLeaveThem() {
        assertEquals(List.of("0"), bordersOf("x: Int, c: Int",
                "c == Int.floorMod(9223372036854775807 * x, 11)"));
        // And where it is computed at them, the same form is: three times the number is.
        assertEquals(List.of("-1", "11", "0"), bordersOf("x: Int, c: Int",
                "c == Int.floorMod(3 * x, 11)"));
        // Moved by a number, the sum with the number is worked out on every row, and it is asked
        // at the values the rows are built at as it was written: it comes to a number an Int
        // holds there, so the form is computed at them all the same.
        assertEquals(List.of("-1", "11", "0"), bordersOf("x: Int, c: Int",
                "c == Int.floorMod(3 * x + 5, 11)"));
        // And moved by a number that overflows at them, the sum is no row's: the quantity holds
        // that number taken by the divisor, which is a small one, so only the sum as written
        // says so.
        assertEquals(List.of("0"), bordersOf("x: Int, c: Int",
                "c == Int.floorMod(3 * x + 9223372036854775807, 11)"));
        assertEquals(List.of("0"), bordersOf("x: Int, c: Int",
                "c == Int.floorMod(3 * x - 9223372036854775807 - 10, 11)"));
    }


    /**
     * A number the form is moved by is an operation over the other numbers of the form as well as
     * the witness, and those stand at whatever value their rows put them at: {@code a + 5} stops
     * at the greatest {@code Int} for {@code a} however {@code x} is chosen. So the operation is
     * not the witness's to get past, the number {@code a} is not said to be left every remainder,
     * and no line is drawn on the remainder — whether {@code a} is free or held where there is no
     * row at all.
     */
    @Test
    void aNumberBesideTheWitnessIsNotSaidToBeLeftEveryRemainderWhereTheFormIsMovedByAConstant() {
        Compilation free = compiled("", "a: Int, x: Int, c: Int",
                "c == Int.floorMod(a + 5 + x, 11)");
        assertEquals(List.of("0"), bordersOf(linesOf(free)));
        assertTrue(notShownAt(free, "a"), () -> reasonsEach("a: Int, x: Int, c: Int",
                "c == Int.floorMod(a + 5 + x, 11)").toString());
        Compilation held = compiled("data Top = Int\n    invariant value == 9223372036854775807\n",
                "a: Top, x: Int, c: Int", "c == Int.floorMod(a.value + 5 + x, 11)");
        assertFalse(bordersOf(linesOf(held)).contains("11"));
        assertFalse(bordersOf(linesOf(held)).contains("-1"));
        // And with no number to move it by, the sum is the form itself and the lines are drawn.
        assertEquals(List.of("-1", "11", "0"), bordersOf("a: Int, x: Int, c: Int",
                "c == Int.floorMod(a + x, 11)"));
    }

    private static boolean notShownAt(Compilation compilation, String place) {
        return compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f").notRead()
                .stream().anyMatch(each -> each.at().equals(place) && each.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE);
    }

    /**
     * A number beside the remainder that is read off a place the form is read at is not apart from
     * it, and the relation is not read as a remainder beside a number.
     */
    @Test
    void aNumberBesideTheRemainderReadOffAPlaceOfItsFormIsNotApartFromIt() {
        assertEquals(List.of(), bordersOf("a: Int, b: Int",
                "Int.floorMod(a + b, 11) == Int.floorMod(a, 3)"));
    }

    /** And one read off another place does, which is what the case above is told apart from. */
    @Test
    void aNumberReadOffAnotherPlaceIsWhatTakesTheFormThroughEveryRemainder() {
        assertEquals(1, reasonsEach("x: Int, xs: List<Int>, c: Int",
                "c == Int.floorMod(x + List.length(xs), 4)").stream()
                .filter(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES::equals).count());
    }

    /**
     * And a number the remainder is of alone is divided by it: with {@code a} put at a value the
     * remainder is that value's, so the number is not said to leave the relation either way.
     */
    @Test
    void theOnlyNumberOfTheFormIsNotSaidToBeLeftUndivided() {
        assertEquals(List.of(), reasonsEach("a: Int, c: Int",
                "c == Int.floorMod(2 * a, 11)").stream()
                .filter(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES::equals).toList());
    }

    /**
     * The numbers a remainder shares with the form it is added to are not read, and are said not
     * to be, rather than read as a relation they are not.
     */
    @Test
    void aRemainderAddedToANumberOfItsOwnFormIsNotRead() {
        assertEquals(List.of(), bordersOf("a: Int, b: Int", "a == Int.floorMod(a + b, 11)"));
    }

    /**
     * A rule of the decision a remainder of a form decides is composed a row on each side: a pair
     * whose form leaves a remainder that meets it, and one whose form leaves one that does not,
     * each worked out here of the pair the row holds. Weighed and moved forms alike, and a
     * remainder met by several values.
     */
    @Test
    void eachRuleOfADecisionOnARemainderIsComposedARowThatTakesIt() {
        record Case(String condition, BiPredicate<Long, Long> holds) {}
        for (Case each : List.of(
                new Case("Int.floorMod(3 * a - d + 2, 10) == 0",
                        (a, d) -> Math.floorMod(3 * a - d + 2, 10L) == 0),
                new Case("Int.floorMod(a - d, 7) >= 5",
                        (a, d) -> Math.floorMod(a - d, 7L) >= 5),
                new Case("2 * Int.floorMod(a + 4 * d, 9) < 3",
                        (a, d) -> 2 * Math.floorMod(a + 4 * d, 9L) < 3))) {
            Compilation compilation = compiled("a: Int, d: Int", each.condition());
            List<Boolean> sides = new ArrayList<>();
            Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("f")
                    .generation().stream()
                    .filter(found -> found.finding().about() instanceof About.ARuleNoRowTakes)
                    .forEach(found -> {
                        if (found.outcome() instanceof GenerationOutcome.Generated made) {
                            made.candidates().forEach(row -> sides.add(each.holds().test(
                                    Long.parseLong(row.inputs().get(0).text()),
                                    Long.parseLong(row.inputs().get(1).text()))));
                        }
                    });
            assertTrue(sides.contains(true) && sides.contains(false),
                    () -> each.condition() + ": a row on each side, and not " + sides);
        }
    }

    /**
     * A remainder of what the code points of a formatted string come to less as many of one
     * number as the string is long — a digit's value, summed — is written a row at each point of
     * its line: thirteen digits whose values leave the remainder the point is for, worked out here
     * of the string the row holds. The length is walked from the format's own, and what the code
     * points come to is what the remainder leaves to be chosen.
     */
    @Test
    void aRemainderOfADigitSumIsWrittenADigitStringAtEachPoint() {
        Compilation compilation = compiled("data Code = String\n"
                        + "    invariant String.matches(\"[0-9]{13}\", value)", "c: Code",
                "Int.floorMod(List.sum(List.map((x) -> x - 48, String.codePoints(c.value))), 10)"
                        + " == 0");
        List<String> labels = new ArrayList<>();
        for (Row row : certifiedRows(linesOf(compilation))) {
            String text = row.inputs().get(0);
            String digits = text.substring(text.indexOf('"') + 1, text.lastIndexOf('"'));
            assertTrue(digits.matches("[0-9]{13}"), text);
            long remainder = Math.floorMod(digits.chars().map(c -> c - '0').sum(), 10);
            for (String label : row.labels()) {
                if (label.contains(" = ")) {
                    assertEquals(Long.parseLong(label.substring(label.lastIndexOf(' ') + 1)),
                            remainder, label + " at " + text);
                    labels.add(label.substring(label.lastIndexOf(' ') + 1));
                } else if (label.contains(" < ")) {
                    assertTrue(remainder > 1, label + " at " + text);
                    labels.add("above");
                }
            }
        }
        assertEquals(List.of("0", "1", "above"), labels.stream().sorted().toList(),
                "a row at the line, beside it and past it");
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

    /** The reason of each place left unread, each once and in the order they were read. */
    private static List<UndividedPosition.Reason> reasonsEach(String parameters,
                                                              String condition) {
        return measured(parameters, condition).notRead().stream()
                .map(PartitionEvidence.NotRead::reason).toList();
    }

    private static List<UndividedPosition.Reason> reasonsOf(String parameters, String condition) {
        return measured(parameters, condition).notRead().stream()
                .map(PartitionEvidence.NotRead::reason).distinct().toList();
    }
}
