package souther.compiler.partition;

import org.junit.jupiter.api.Test;

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

import java.math.BigInteger;
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
 * holds that element. Every other element leaves what one of those leaves. A run working the sum
 * out is read as it was, so a sum past its type is not taken away by reading the division as a
 * remainder.
 *
 * <p>Held to the lines the rule puts there, worked out here from the elements, and to the rows as
 * they ran and were read back.
 */
class ARemainderOverAnElementOfAListOfWholeNumbersIsReadAsARemainderTest {

    /** {@code Int.floorMod(a + n, 7)} over {@code List.rangeInclusive(0, days)} is a remainder
     *  of {@code a} and of the element, which is the number the walk hands in turn. */
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
    }

    /** The same remainder over an element of a list of the input is one of the input's numbers
     *  alone, as it was. */
    @Test
    void aRemainderOfTheInputsNumbersIsReadAtThem() {
        Quantity.RemainderOfADividend remainder = theRemainderStated("a: Int, xs: List<Int>",
                "List.any(n -> Int.floorMod(a + n, 7) >= 1, xs)");
        assertNotNull(remainder.overTheInput(), remainder::toString);
    }

    /**
     * A list written with one element, six or seven is read on each element, and each leaves
     * {@code a} its own remainder to be at for the comparison to hold: one remainder for one
     * element, six for six — so some remainder of {@code a} leaves the list nothing — and every
     * remainder for seven.
     */
    @Test
    void aListOfWholeNumbersWrittenOutPutsALineAtEachRemainderAnElementLeaves() {
        for (int last : List.of(0, 5, 6)) {
            Compilation compilation = compiled("a: Int", "List<Int>",
                    "List.rangeInclusive(0, %d) |> %s".formatted(last, AT_NOUGHT));
            Set<String> lines = new TreeSet<>();
            Set<String> expected = new TreeSet<>();
            for (int element = 0; element <= last; element++) {
                expected.add("Int.floorMod(a, 7) = " + Math.floorMod(-element, 7));
            }
            measured(compilation).forEach(line -> lines.add(line.left() + " = " + line.value()));
            assertEquals(expected, lines, "a list of " + (last + 1));
            measured(compilation).forEach(line -> assertRowsStandWhereTheyAreOwed(line, 0));
        }
    }

    /**
     * Over {@code List.rangeInclusive(3, days)}, the comparison is read on the elements three to
     * nine, the seven the divisor comes round in: a line on what each leaves of {@code a}, and a
     * row at it makes the list hold that element.
     */
    @Test
    void anElementOfAListToAnInputsNumberIsReadAtTheElementsTheListStartsWith() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "List.rangeInclusive(3, days) |> " + AT_NOUGHT);
        assertEquals(theLinesOfTheFirstSeven(3, "0"), linesOn(compilation));
        measured(compilation).forEach(line -> assertRowsStandWhereTheyAreOwed(line, 3));
    }

    /** {@code >= 5} holds at two remainders of seven, and each element's line is where those
     *  two start. */
    @Test
    void aComparisonHoldingAtSeveralRemaindersIsALineOnEachElement() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "List.rangeInclusive(0, days) |> List.filter(n -> Int.floorMod(a + n, 7) >= 5)");
        assertEquals(theLinesOfTheFirstSeven(0, "5"), linesOn(compilation));
        measured(compilation).forEach(line -> assertRowsStandWhereTheyAreOwed(line, 0));
    }

    /** A row whose sum over some element passes the type stops there, and no such row is shown
     *  to stand at a line: the run working the sum out is read as it was. */
    @Test
    void noRowWhoseSumPassesItsTypeIsShownAtALine() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "if a >= 9223372036854775805 then List.rangeInclusive(0, days) |> "
                        + AT_NOUGHT + " else []");
        List<ObservedInputs> rows = new ArrayList<>();
        measured(compilation).stream().filter(line -> shiftOf(line.left()) != null)
                .forEach(line -> line.items().values().forEach(item -> rows.addAll(
                        certified(item))));
        assertFalse(rows.isEmpty(), "some line has its rows");
        BigInteger most = BigInteger.valueOf(Long.MAX_VALUE);
        for (ObservedInputs row : rows) {
            assertTrue(BigInteger.valueOf(number(row, 0)).add(BigInteger.valueOf(number(row, 1)))
                    .compareTo(most) <= 0, row::toString);
        }
    }

    /** An operation that stops at the first element meeting the comparison makes it on a later
     *  one only where none before met it, so it is read on none of them: no line, and the rule is
     *  said not read, so the body is not measured complete. */
    @Test
    void noLineIsDrawnWhereTheOperationStopsAtAnAnswer() {
        Compilation compilation = compiled("a: Int, days: Int", "Bool",
                "List.any(n -> Int.floorMod(a + n, 7) >= 1, List.rangeInclusive(0, days))");
        assertEquals(Set.of(), linesOn(compilation));
        assertTrue(report(compilation).contains("· not read: comparison@"),
                () -> report(compilation));
    }

    /** A divisor past how many readings one condition is read in is read on no element, and
     *  says so. */
    @Test
    void aDivisorPastTheReadingsIsReadOnNoElement() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "List.rangeInclusive(0, days) |> List.filter(n -> Int.floorMod(a + n, 1000) == 0)");
        assertEquals(Set.of(), linesOn(compilation));
        assertTrue(report(compilation).contains("READINGS_OF_ONE_CONDITION"),
                () -> report(compilation));
    }

    private static final String AT_NOUGHT = "List.filter(n -> Int.floorMod(a + n, 7) == 0)";

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
                    long element = from + Math.floorMod(shift - from, 7);
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
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The one remainder the last comparison of {@code m} states. */
    private static Quantity.RemainderOfADividend theRemainderStated(String parameters,
                                                                   String body) {
        Compilation compilation = compiled(parameters, "Bool", body);
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
                CountWitnesses.AtComparisons.NONE).comparisons();
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
            case Proposition.All(var parts, var _) -> parts.forEach(each -> remaindersIn(each, into));
            case Proposition.Any(var parts, var _) -> parts.forEach(each -> remaindersIn(each, into));
            case Proposition.Compared(Relation.Affine(var form, var _), var _, var _) ->
                    form.coefs().keySet().forEach(each -> {
                        if (each instanceof Quantity.RemainderOfADividend remainder) {
                            into.add(remainder);
                        }
                    });
            default -> { }
        }
    }

    private static Compilation compiled(String parameters, String answer, String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (%s) -> %s
                let m (%s) = %s
                """.formatted(parameters, answer, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""),
                body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return compilation;
    }
}
