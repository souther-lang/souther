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
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a division leaves of a sum over the element of a list of every whole number between two
 * is read as the remainder it is, of the element and of the input's numbers together, and not as
 * a value nothing is said of.
 *
 * <p>The meaning and no more. The element is no number a row holds, so no row is put at the
 * remainder and no line is drawn on it; and a run working the sum out is read as it was, so a sum
 * past its type is not taken away by reading the division as a remainder.
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

    /** No line is drawn on a remainder no row's numbers put anywhere, and the rule is said not
     *  read, so the body is not measured complete. */
    @Test
    void noLineIsDrawnOnARemainderOfTheElement() {
        Compilation compilation = compiled("a: Int, days: Int",
                "List.any(n -> Int.floorMod(a + n, 7) >= 1, List.rangeInclusive(0, days))");
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "w1").get("m");
        assertTrue(lines == null || lines.stream().noneMatch(line -> line.left().equals("a")),
                () -> String.valueOf(lines));
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("· not read: comparison@"), report);
    }

    /** The one remainder the last comparison of {@code m} states. */
    private static Quantity.RemainderOfADividend theRemainderStated(String parameters,
                                                                   String body) {
        Compilation compilation = compiled(parameters, body);
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

    private static Compilation compiled(String parameters, String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(parameters, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), body),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return compilation;
    }
}
