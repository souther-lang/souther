package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.OnOneElement;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A case weighing the element of {@code List.rangeInclusive(0, days)} and holding it to a
 * congruence, {@code floorMod(w·n + a + c, m) == 0} beside {@code n >= k}, holds at a row exactly
 * where some element of the row's list meets both, and the values of the congruence's class are
 * worked out from the row rather than tried.
 *
 * <p>Held against every element of the list, over small divisors, weights a divisor shares a part
 * with and nought among them, constants, and rows whose list is empty. Then over a divisor no walk
 * of the values to its class's first could finish: the case is answered from the class. And where
 * the values past the walked ones are left, the row is one this could not tell of, never one the
 * case fails at.
 */
class AnElementComesRoundToTheClassItsCongruenceLeavesAtTheRowTest {

    /** The reading of {@code m}, the element the range hands its closure, and {@code a}. */
    private record Read(InputReading reading, Quantity.OfABinding element, Quantity a,
                        Quantity.RemainderOfADividend remainder) {}

    private static final Read READ = read();

    @Test
    void theCaseHoldsWhereSomeElementOfTheListMeetsIt() {
        for (int divisor : new int[] {1, 2, 3, 4, 6, 7}) {
            for (int weight = -2; weight <= 3; weight++) {
                for (int constant : new int[] {0, 1, -2}) {
                    for (int least : new int[] {0, 3, 8}) {
                        ACaseAskedAtSomeElement asked = asked(weight, constant, divisor, least);
                        for (int a = -3; a <= 3; a++) {
                            for (int days : new int[] {-1, 0, 1, 5, 11}) {
                                boolean some = false;
                                for (int n = 0; n <= days; n++) {
                                    some |= Math.floorMod(weight * n + a + constant, divisor) == 0
                                            && n >= least;
                                }
                                String said = "floorMod(" + weight + "·n + " + a + " + "
                                        + constant + ", " + divisor + ") == 0 && n >= " + least
                                        + " over 0.." + days;
                                assertEquals(some ? AStatementAtARow.Answer.HOLDS
                                        : AStatementAtARow.Answer.FAILS, asked.at(row(a, days)),
                                        said);
                            }
                        }
                    }
                }
            }
        }
    }

    @Test
    void theClassOfALargeDivisorIsWorkedOutAndNotWalkedTo() {
        int divisor = 1_000_000_007;
        ACaseAskedAtSomeElement asked = asked(1, 0, divisor, 0);
        assertTimeoutPreemptively(Duration.ofSeconds(10), () -> {
            assertEquals(AStatementAtARow.Answer.HOLDS, asked.at(row(5, 2_000_000_000)),
                    "the first element the class holds is the divisor less five");
            assertEquals(AStatementAtARow.Answer.FAILS, asked.at(row(5, 1_000)),
                    "the first is past the end of the list");
        });
        ACaseAskedAtSomeElement even = asked(2, 0, 4, 0);
        assertEquals(AStatementAtARow.Answer.FAILS, even.at(row(1, 2_000_000_000)),
                "twice a number and an odd one leave something by four, whatever the number");
    }

    @Test
    void valuesLeftPastTheWalkedOnesAreNotValuesTheCaseFailsAt() {
        ACaseAskedAtSomeElement asked = asked(1, 0, 1, 5_000);
        assertInstanceOf(AStatementAtARow.Answer.CouldNotTell.class, asked.at(row(0, 4_000)),
                "the walk stops before the list's end, with no element tried meeting the case");
    }

    /** {@code floorMod(weight·n + a + constant, divisor) == 0 && n >= least}, asked at some
     *  element. */
    private static ACaseAskedAtSomeElement asked(int weight, int constant, int divisor,
                                                 int least) {
        Map<Quantity, ExactRatio> dividend = new LinkedHashMap<>();
        dividend.put(READ.element(), ExactRatio.of(weight));
        dividend.put(READ.a(), ExactRatio.ONE);
        Quantity remainder = new Quantity.RemainderOfADividend(READ.remainder().operation(),
                new LinearForm<>(ExactRatio.of(constant), dividend), BigInteger.valueOf(divisor));
        Proposition stated = Proposition.all(List.of(
                compared(new LinearForm<>(ExactRatio.ZERO, Map.of(remainder, ExactRatio.ONE)),
                        Rel.EQ),
                compared(new LinearForm<>(ExactRatio.of(-least),
                        Map.of(READ.element(), ExactRatio.ONE)), Rel.GE)));
        return ACaseAskedAtSomeElement.of(stated, "m", READ.reading().quantities(),
                new ConcurrentHashMap<>()).orElseThrow();
    }

    private static Proposition compared(LinearForm<Quantity> form, Rel rel) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, rel);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }

    /** A row holding {@code a} and {@code days}. */
    private static BorderQuantity.Observation row(long a, long days) {
        return new BorderQuantity.Observation() {
            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return switch (path.toString()) {
                    case "a" -> WalkResult.reached(
                            new ObservationAtPoint.Value(new ObservedValue.Integer(a)));
                    case "days" -> WalkResult.reached(
                            new ObservationAtPoint.Value(new ObservedValue.Integer(days)));
                    default -> throw new AssertionError("the row holds a and days: " + path);
                };
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a case of numbers is read at one value: " + path);
            }

            @Override
            public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
                throw new AssertionError("a case of numbers holds no container: " + container);
            }
        };
    }

    /** The reading of {@code floorMod(a + n, 7) == 0} over the elements of
     *  {@code List.rangeInclusive(0, days)}, and the numbers its remainder weighs. */
    private static Read read() {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (a: Int, days: Int) -> Bool
                let m (a, days) = List.any(n -> Int.floorMod(a + n, 7) == 0,
                                           List.rangeInclusive(0, days))
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
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
        Proposition stated = WhatConditionsState.of(read).comparison(comparison, last.reads(), read)
                .stated().proposition();
        Quantity.OfABinding element = OnOneElement.theElementOf(stated).orElseThrow();
        List<Quantity.RemainderOfADividend> found = new ArrayList<>();
        remaindersIn(stated, found);
        assertEquals(1, found.size(), found::toString);
        Quantity a = found.getFirst().dividend().coefs().keySet().stream()
                .filter(DecisionAtom.OfTheInput.class::isInstance).findFirst().orElseThrow();
        return new Read(read, element, a, found.getFirst());
    }

    private static void remaindersIn(Proposition stated,
                                     List<Quantity.RemainderOfADividend> into) {
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
}
