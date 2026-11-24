package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.UnreadBesideItsStops;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Towards;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a division leaves of a sum over the element of a list of every whole number between two
 * is read as the remainder it is, of the element and of the input's numbers together, and not as
 * a value nothing is said of.
 *
 * <p>The element is no number a row holds, so no line is drawn on that remainder. The comparison
 * is read on the elements the list starts with instead, as many as the divisor comes round in:
 * on each, the remainder is one of the input's numbers alone, and its line decides where the list
 * holds that element. Every other element leaves what one of those leaves. Relations held together
 * are read the same way, on as many elements as all their divisors come round in.
 *
 * <p>Held to the lines the rule puts there, worked out here from the elements, and to the rows as
 * they ran and were read back. Which statements come round, and in how many elements, is held by
 * {@code AStatementComesRoundOnlyWhereEveryElementThatFarApartComesOutAlikeTest} and
 * {@code TheFirstElementsOfAListStandForEveryElementOfItTest}; a walk stopping at the first
 * element a membership chose by {@code EveryPublishedReasonIsWrittenBySomeCompilationTest}; and
 * a run working the sum out, read as it was so that a sum past its type is not taken away by
 * reading the division as a remainder, by
 * {@code AnOperationPastItsTypeStopsEveryRunThatGetsToItsComparisonTest}. A test that reads no
 * row measures nothing.
 */
class ARemainderOverAnElementOfAListOfWholeNumbersIsReadAsARemainderTest {

    /** {@code Int.floorMod(a + n, 7)} over {@code List.rangeInclusive(0, days)} is a remainder
     *  of {@code a} and of the element, which is the number the walk hands in turn; over an
     *  element of a list of the input it is one of the input's numbers alone. */
    @Test
    void theRemainderIsOfTheElementAndTheInputTogether() {
        Quantity.RemainderOfADividend remainder = theRemainderStated("a: Int, days: Int",
                "List.any(n -> Int.floorMod(a + n, 7) >= 1, List.rangeInclusive(0, days))");
        assertEquals(2, remainder.dividend().coefs().size(), remainder::toString);
        assertTrue(remainder.dividend().coefs().containsKey(
                new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("a")))),
                remainder::toString);
        assertTrue(remainder.dividend().coefs().keySet().stream().anyMatch(each ->
                each instanceof Quantity.OfABinding bound && bound.handed().orElse(null)
                        instanceof Quantity.AWholeNumberInTurn), remainder::toString);
        assertNull(remainder.overTheInput(), "no row holds the element");
        Quantity.RemainderOfADividend ofTheInput = theRemainderStated("a: Int, xs: List<Int>",
                "List.any(n -> Int.floorMod(a + n, 7) >= 1, xs)");
        assertNotNull(ofTheInput.overTheInput(), ofTheInput::toString);
    }

    /** A list written with six elements is read on each, and each leaves {@code a} its own
     *  remainder to be at for the comparison to hold: six of the seven, so one remainder of
     *  {@code a} leaves the list nothing. */
    @Test
    void aListOfWholeNumbersWrittenOutPutsALineAtEachRemainderAnElementLeaves() {
        Compilation compilation = compiled("a: Int", "List<Int>",
                "List.rangeInclusive(0, 5) |> List.filter(n -> Int.floorMod(a + n, 7) == 0)",
                Adequacy.Asked.fullReport());
        Set<String> expected = new TreeSet<>();
        for (int element = 0; element <= 5; element++) {
            expected.add("Int.floorMod(a, 7) = " + Math.floorMod(-element, 7));
        }
        assertEquals(expected, linesOn(compilation));
        measured(compilation).forEach(line -> assertRowsStandWhereTheyAreOwed(line, 0));
    }

    /**
     * Over {@code List.rangeInclusive(3, days)}, the comparison is read on the elements three to
     * nine, the seven the divisor comes round in. {@code >= 5} holds at two remainders of seven,
     * and each element's line is where those two start: a line on what each leaves of {@code a},
     * and a row at it makes the list hold that element.
     */
    @Test
    void anElementOfAListToAnInputsNumberIsReadAtTheElementsTheListStartsWith() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "List.rangeInclusive(3, days) |> List.filter(n -> Int.floorMod(a + n, 7) >= 5)",
                Adequacy.Asked.fullReport());
        assertEquals(theLinesOfTheFirstSeven(3, "5"), linesOn(compilation));
        measured(compilation).forEach(line -> assertRowsStandWhereTheyAreOwed(line, 3));
    }

    /** An operation that stops at the first element meeting the comparison makes it on a later
     *  one only where none before met it, so it is read on none of them: no line, and the rule is
     *  said not read. */
    @Test
    void noLineIsDrawnWhereTheOperationStopsAtAnAnswer() {
        Compilation compilation = compiled("a: Int, days: Int", "Bool",
                "List.any(n -> Int.floorMod(a + n, 7) >= 1, List.rangeInclusive(0, days))",
                NO_ROWS);
        assertEquals(Set.of(), linesOn(compilation));
        assertTrue(UnreadBesideItsStops.in(report(compilation)), () -> report(compilation));
    }

    /** The choice a walk's closure makes, which holds a remainder of the element and a membership,
     *  and a filter that asks a set of what the choice made. The filter is handed every element
     *  the walk made, so it is read on the elements the list starts with, and what it states
     *  there is a relation between the set and the input's numbers, which is said as that and not
     *  as a remainder no position holds. */
    @Test
    void aRemainderBesideAMembershipOfTheChoiceIsReadWhereTheFilterIsMadeOnEveryElement() {
        String report = report(compiled("hs: Set<Int>, from: Int, days: Int", "List<Int>",
                "List.rangeInclusive(0, days)"
                        + " |> List.map(n -> if Int.floorMod(from + n, 2) >= 1"
                        + " && Bool.not(Set.contains(from + n, hs))"
                        + " then from + n else from + n + 1)"
                        + " |> List.filter(d -> Set.contains(d, hs))", NO_ROWS));
        assertFalse(report.contains("about what a division leaves of a number the body works"
                + " out, which no position holds"), report);
        List<String> notRead = report.lines().filter(line -> line.contains("· not read:")
                && !line.contains(UnreadBesideItsStops.STOPS_NOT_ALL_TOLD)).toList();
        assertFalse(notRead.isEmpty(), report);
        notRead.forEach(line -> assertTrue(
                line.contains("relates the value here to another value"), line + "\n" + report));
    }

    /** A divisor past how many readings one condition is read in is read on no element, and
     *  says so. */
    @Test
    void aDivisorPastTheReadingsIsReadOnNoElement() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "List.rangeInclusive(0, days) |> List.filter(n -> Int.floorMod(a + n, 1000) == 0)",
                NO_ROWS);
        assertEquals(Set.of(), linesOn(compilation));
        assertTrue(report(compilation).contains("READINGS_OF_ONE_CONDITION"),
                () -> report(compilation));
    }

    /**
     * A comparison holding several relations together over the element is read on as many
     * elements as all their divisors come round in, and each line decides where the statement
     * turns on it on one of those: a line on what {@code a} leaves of three where {@code b} is
     * above nought, and one on what it leaves of two where it is not. The lines are those every
     * element puts, worked out here over elements well past where they come round, and every row
     * read back is on the side of {@code b} the line decides on, with the list holding an element
     * that leaves {@code a} what the line is on.
     */
    @Test
    void relationsHeldTogetherAreReadOnTheElementsAllTheirDivisorsComeRoundIn() {
        Compilation compilation = compiled("a: Int, b: Int, days: Int", "List<Int>",
                "List.rangeInclusive(0, days) |> List.filter(n -> (if b > 0 then"
                        + " Int.floorMod(a + n, 3) else Int.floorMod(a + n, 2) + 1) >= 2)",
                Adequacy.Asked.fullReport());
        Set<String> expected = new TreeSet<>();
        for (int element = 0; element < 48; element++) {
            expected.add(remainderOf("a", element, 3) + " = 2");
            expected.add(remainderOf("a", element, 2) + " = 1");
        }
        assertEquals(expected, gatedLinesOn(compilation));
        assertFalse(UnreadBesideItsStops.in(report(compilation)), () -> report(compilation));
        measured(compilation).stream().filter(line -> gatedShiftOf(line.left()) != null)
                .forEach(ARemainderOverAnElementOfAListOfWholeNumbersIsReadAsARemainderTest
                        ::assertGatedRowsDecideOnAnElementTheListHolds);
    }

    /**
     * The first of two numbers from {@code a} and the element that is odd and is no number a set
     * holds, compared on each element: the search stops at the first, so a line on what the later
     * one leaves decides only where the one before did not stop it. Whether a
     * number is in the set turns on the element itself and does not come round, so it is asked of
     * a row at an element the row holds, and not at the one the remainders come round to. Each row
     * read back is one whose run, on some element its list holds and with the set it holds, works
     * out the remainder the line is on.
     */
    @Test
    void aSearchPassingOverTheNumbersOfASetIsAskedAtTheElementItself() {
        Compilation compilation = compiled("a: Int, hs: Set<Int>, days: Int", "List<Int>",
                "List.rangeInclusive(0, days) |> List.filter(n -> Int.floorMod("
                        + "List.rangeInclusive(0, " + (CANDIDATES - 1) + ")"
                        + " |> List.map(j -> a + n + j)"
                        + " |> List.find(d -> Int.floorMod(d, 2) >= 1"
                        + " && Bool.not(Set.contains(d, hs)))"
                        + " |> Option.withDefault(a + n), 2) == 0)",
                Adequacy.Asked.fullReport());
        String report = report(compilation);
        // What the set's numbers are related to is the element itself, which values of the set
        // settle that is not worked out, and it is said so; nothing else is left unread.
        report.lines().filter(line -> line.contains("· not read:")
                && !line.contains(UnreadBesideItsStops.STOPS_NOT_ALL_TOLD)).forEach(line ->
                assertTrue(line.contains("relates the value here to another value"),
                        () -> line + "\n" + report));
        List<BorderAssessment> owed = measured(compilation).stream()
                .filter(line -> searchedShiftOf(line.left()) != null).toList();
        assertFalse(owed.isEmpty(), report);
        List<ObservedInputs> rows = new ArrayList<>();
        for (BorderAssessment line : owed) {
            int shift = searchedShiftOf(line.left());
            line.items().forEach((point, item) -> certified(item).forEach(row -> {
                rows.add(row);
                long a = number(row, 0);
                Set<Long> hs = numbersIn(row, 1);
                long days = number(row, 2);
                boolean worked = false;
                for (int element = 0; element <= Math.min(days, 48); element++) {
                    worked |= theSearchWorksOut(a, hs, element).contains(shift);
                }
                assertTrue(worked, () -> line.left() + " " + point + " is worked out on an"
                        + " element the list holds: " + row);
            }));
        }
        assertFalse(rows.isEmpty(), "some line has its rows");
    }

    /** How a test that reads no row compiles its model: the lines and the report, with nothing
     *  measured. */
    private static final Adequacy.Asked NO_ROWS = new Adequacy.Asked(Adequacy.Level.OFF, false);

    /** How many numbers from {@code a} and the element the search looks at. */
    private static final int CANDIDATES = 2;

    /** The whole numbers the set at {@code parameter} holds in {@code row}. */
    private static Set<Long> numbersIn(ObservedInputs row, int parameter) {
        if (!(row.inputs().get(parameter) instanceof ObservedValue.Sequence(var elements))) {
            throw new AssertionError("a set: " + row);
        }
        Set<Long> out = new TreeSet<>();
        elements.forEach(each -> {
            if (!(each instanceof ObservedValue.Integer(long value))) {
                throw new AssertionError("a whole number: " + row);
            }
            out.add(value);
        });
        return out;
    }

    /** The remainders of two whose shift from {@code a} the search on {@code element} works out
     *  on a run from {@code a}, passing over the numbers in {@code hs}: each candidate up to the
     *  first odd one, and the one compared at the end. */
    private static Set<Integer> theSearchWorksOut(long a, Set<Long> hs, int element) {
        Set<Integer> out = new TreeSet<>();
        long landed = a + element;
        for (int j = 0; j < CANDIDATES; j++) {
            out.add(Math.floorMod(element + j, 2));
            if (Math.floorMod(a + element + j, 2) >= 1 && !hs.contains(a + element + j)) {
                landed = a + element + j;
                break;
            }
        }
        out.add(Math.floorMod(landed - a, 2));
        return out;
    }

    private static final Pattern SEARCHED_REMAINDER =
            Pattern.compile("Int\\.floorMod\\(a(?: \\+ (\\d+))?, 2\\)");

    /** What {@code a} is moved by in {@code left}, or null where it is no remainder of it by
     *  two. */
    private static Integer searchedShiftOf(String left) {
        Matcher matcher = SEARCHED_REMAINDER.matcher(left);
        return !matcher.matches() ? null
                : matcher.group(1) == null ? 0 : Integer.parseInt(matcher.group(1));
    }

    private static final Pattern GATED_REMAINDER =
            Pattern.compile("Int\\.floorMod\\(a(?: \\+ (\\d+))?, ([23])\\)");

    /** How {@code a} or {@code b} is written moved by the element {@code element}, by whole
     *  turns of {@code divisor}. */
    private static String remainderOf(String input, int element, int divisor) {
        int moved = Math.floorMod(element, divisor);
        return moved == 0 ? "Int.floorMod(" + input + ", " + divisor + ")"
                : "Int.floorMod(" + input + " + " + moved + ", " + divisor + ")";
    }

    /** What the input in {@code left} is moved by, or null where it is none of the two
     *  remainders. */
    private static Integer gatedShiftOf(String left) {
        Matcher matcher = GATED_REMAINDER.matcher(left);
        return !matcher.matches() ? null
                : matcher.group(1) == null ? 0 : Integer.parseInt(matcher.group(1));
    }

    /** The lines of {@code m} on a remainder of {@code a} by three or by two. */
    private static Set<String> gatedLinesOn(Compilation compilation) {
        Set<String> out = new TreeSet<>();
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "w1").get("m");
        if (lines != null) {
            lines.stream().filter(line -> gatedShiftOf(line.left()) != null)
                    .forEach(line -> out.add(line.left() + " = " + line.value()));
        }
        return out;
    }

    /**
     * Every row read back at every item owed of {@code line} stands where the item is, on the side
     * of {@code b} the statement turns on the line, and holds an element the list holds that
     * leaves {@code a} the remainder the line is on.
     */
    private static void assertGatedRowsDecideOnAnElementTheListHolds(BorderAssessment line) {
        Matcher matcher = GATED_REMAINDER.matcher(line.left());
        assertTrue(matcher.matches(), line::left);
        int shift = matcher.group(1) == null ? 0 : Integer.parseInt(matcher.group(1));
        int divisor = Integer.parseInt(matcher.group(2));
        long level = Long.parseLong(line.value());
        line.items().forEach((point, item) -> {
            if (!(item instanceof ItemAssessment.Owed)) {
                return;
            }
            List<ObservedInputs> rows = certified(item);
            assertFalse(rows.isEmpty(), () -> line.left() + " " + point + " has a row: " + item);
            for (ObservedInputs row : rows) {
                long a = number(row, 0);
                long b = number(row, 1);
                long days = number(row, 2);
                long left = Math.floorMod(a + shift, divisor);
                boolean there = switch (point) {
                    case DomainPoint.AtTheLine _ -> left == level;
                    case DomainPoint.BesideTheLine(Towards side) ->
                            left == (side == Towards.ABOVE ? level + 1 : level - 1);
                    case DomainPoint.InTheRegion(Towards side) ->
                            side == Towards.ABOVE ? left > level : left < level;
                };
                assertTrue(there, () -> line.left() + " " + point + ": " + row);
                assertEquals(divisor == 3, b > 0,() -> line.left() + " " + point
                        + " is on the side of b it decides on: " + row);
                assertTrue(days >= shift, () -> line.left() + " " + point
                        + " holds an element that leaves a what the line is on: " + row);
            }
        });
    }

    private static final Pattern REMAINDER =
            Pattern.compile("Int\\.floorMod\\(a(?: \\+ (\\d+))?, 7\\)");

    /** The lines on what each of the seven elements from {@code from} leaves of {@code a}, each at
     *  {@code level}: the remainder of {@code a} moved by the element, by whole turns of seven. */
    private static Set<String> theLinesOfTheFirstSeven(int from, String level) {
        Set<String> out = new TreeSet<>();
        for (int at = 0; at < 7; at++) {
            int moved = Math.floorMod(from + at, 7);
            out.add((moved == 0 ? "Int.floorMod(a, 7)" : "Int.floorMod(a + " + moved + ", 7)")
                    + " = " + level);
        }
        return out;
    }

    /** What {@code a} is moved by in {@code left}, or null where it is no remainder of it. */
    private static Integer shiftOf(String left) {
        Matcher matcher = REMAINDER.matcher(left);
        return !matcher.matches() ? null
                : matcher.group(1) == null ? 0 : Integer.parseInt(matcher.group(1));
    }

    /**
     * Every row read back at every item owed of {@code line} leaves {@code a} the remainder the
     * item is at, and, where the list runs to {@code days}, holds the element the line was read
     * on: the one past {@code from} that moves {@code a} as the line does.
     */
    private static void assertRowsStandWhereTheyAreOwed(BorderAssessment line, int from) {
        Integer shift = shiftOf(line.left());
        assertNotNull(shift, line::left);
        long level = Long.parseLong(line.value());
        line.items().forEach((point, item) -> {
            if (!(item instanceof ItemAssessment.Owed)) {
                return;
            }
            List<ObservedInputs> rows = certified(item);
            assertFalse(rows.isEmpty(), () -> line.left() + " " + point + " has a row: " + item);
            for (ObservedInputs row : rows) {
                long left = Math.floorMod(number(row, 0) + shift, 7);
                boolean there = switch (point) {
                    case DomainPoint.AtTheLine _ -> left == level;
                    case DomainPoint.BesideTheLine(Towards side) ->
                            left == (side == Towards.ABOVE ? level + 1 : level - 1);
                    case DomainPoint.InTheRegion(Towards side) ->
                            side == Towards.ABOVE ? left > level : left < level;
                };
                assertTrue(there, () -> line.left() + " " + point + ": " + row);
                if (row.inputs().size() > 1) {
                    long element = (long) from + Math.floorMod(shift - from, 7);
                    assertTrue(number(row, 1) >= element, () -> line.left() + " " + point
                            + " holds " + element + ": " + row);
                }
            }
        });
    }

    private static List<ObservedInputs> certified(ItemAssessment item) {
        return item instanceof ItemAssessment.Owed owed ? owed.searches().each().stream()
                .filter(ItemAssessment.Attempt.Certified.class::isInstance)
                .map(ItemAssessment.Attempt.Certified.class::cast)
                .map(ItemAssessment.Attempt.Certified::readBack).toList() : List.of();
    }

    private static long number(ObservedInputs row, int parameter) {
        if (!(row.inputs().get(parameter) instanceof ObservedValue.Integer(long value))) {
            throw new AssertionError("a whole number: " + row);
        }
        return value;
    }

    /** The lines of {@code m} on a remainder of {@code a}, each as where it is. */
    private static Set<String> linesOn(Compilation compilation) {
        Set<String> out = new TreeSet<>();
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "w1").get("m");
        if (lines != null) {
            lines.stream().filter(line -> shiftOf(line.left()) != null)
                    .forEach(line -> out.add(line.left() + " = " + line.value()));
        }
        return out;
    }

    private static List<BorderAssessment> measured(Compilation compilation) {
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "w1").get("m");
        assertNotNull(lines, "m was measured");
        return lines;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The one remainder the last comparison of {@code m} states. */
    private static Quantity.RemainderOfADividend theRemainderStated(String parameters,
                                                                   String body) {
        Compilation compilation = compiled(parameters, "Bool", body, NO_ROWS);
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("m");
        AnalysisBody analysis = checked.analysisBodies().get("m");
        InputReading read = inputs.reading(rules);
        List<ComparisonReadings.Reading> readings = ComparisonReadings.of("m", analysis, read,
                InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                        inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        inputs.dependencies()),
                ComparisonWitnesses.AtComparisons.NONE).comparisons();
        ComparisonReadings.Reading last = readings.getLast();
        if (!(last.statement() instanceof ComparisonReadings.Stated.AComparison(var comparison))) {
            throw new AssertionError("the last statement is a comparison: " + last);
        }
        List<Quantity.RemainderOfADividend> found = new ArrayList<>();
        remaindersIn(WhatConditionsState.of(read).comparison(comparison, last.reads(), read)
                .stated().proposition(), found);
        assertEquals(1, found.size(), found::toString);
        return found.getFirst();
    }

    private static void remaindersIn(Proposition stated, List<Quantity.RemainderOfADividend> into) {
        switch (stated) {
            case Proposition.All(var parts, var _, var _) ->
                    parts.forEach(each -> remaindersIn(each, into));
            case Proposition.Any(var parts, var _, var _) ->
                    parts.forEach(each -> remaindersIn(each, into));
            case Proposition.Compared(Relation.Affine(var form, var _), var _, var _, var _) ->
                    form.coefs().keySet().forEach(each -> {
                        if (each instanceof Quantity.RemainderOfADividend remainder) {
                            into.add(remainder);
                        }
                    });
            default -> { }
        }
    }

    private static Compilation compiled(String parameters, String answer, String body,
                                        Adequacy.Asked asked) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (%s) -> %s
                let m (%s) = %s
                """.formatted(parameters, answer, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""),
                body), "Main");
        compilation.measure(asked);
        return ACompiledModel.compiles(compilation);
    }
}
