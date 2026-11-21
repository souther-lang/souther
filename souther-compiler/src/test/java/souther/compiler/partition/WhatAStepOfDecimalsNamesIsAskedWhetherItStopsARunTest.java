package souther.compiler.partition;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.ACompiledModel;
import souther.compiler.StopsTheReportSays;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A walk of decimals stops a run nowhere of its own, and a step that adds a part of the element
 * works out nothing else on the way to its answer. What it gives a name before that is worked out
 * whether or not anything reads it: a product of two whole numbers there may pass an {@code Int},
 * and a run that gets there stops. The same product of two numbers each at most a thousand stops
 * none, and so does a step naming nothing that may.
 *
 * <p>The stop is said of the product, as a form of the places of the elements, whether a walk's
 * step or a closure a total adds up names it: each is worked out at every element.
 */
class WhatAStepOfDecimalsNamesIsAskedWhetherItStopsARunTest {

    private static final String SOURCE = """
            module d

            data Small = Int
                invariant value >= 0 && value <= 1000
            data M = { a: %1$s, b: %1$s, price: Decimal }
            data W = { ms: List<M> }

            behavior f : (w: W) -> Int

            let f (w) = {
                let t = %2$s
                if t >= 10.0m then 1 else 0
            }
            """;

    /** What the report says, the numbers multiplied of {@code type}, of the total {@code total}
     *  over the months, measured at the readings alone. */
    private static StopsTheReportSays.Said said(String type, String total) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(type, total), "Main");
        compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
        ACompiledModel.compiles(compilation);
        return StopsTheReportSays.of(compilation);
    }

    /** The operations a stop is said of, as written. */
    private static List<String> stoppingIn(StopsTheReportSays.Said said) {
        return said.stops().stream().flatMap(stop -> stop.operations().stream())
                .map(StopsTheReportSays.Operation::written).toList();
    }

    /** Whether a comparison is left unread for a run that may stop where nothing says. */
    private static boolean unreadForAStop(StopsTheReportSays.Said said) {
        return said.unread().stream()
                .anyMatch(each -> each.because().equals("evaluation_stops_not_fully_read"));
    }

    @ParameterizedTest
    @ValueSource(strings = {
            "List.fold((acc, m) -> { let n = %s \n acc + m.price }, 0.0m, w.ms)",
            "List.sum(List.map(m -> { let n = %s \n m.price }, w.ms))",
    })
    void aProductAStepNamesIsSaidToStopTheRunAndHeldWithinAnIntIsNot(String total) {
        StopsTheReportSays.Said wide = said("Int", total.formatted("m.a * m.b"));
        assertEquals(List.of("w.ms[*].a * w.ms[*].b"), stoppingIn(wide), wide::toString);

        StopsTheReportSays.Said small = said("Small", total.formatted("m.a.value * m.b.value"));
        assertEquals(List.of(), stoppingIn(small), () -> "control " + wide + "\n" + small);
        assertFalse(unreadForAStop(small), "control");
    }

    @ParameterizedTest
    @ValueSource(strings = {
            "List.fold((acc, m) -> acc + m.price, 0.0m, w.ms)",
            "List.fold((acc, m) -> { let p = m.price \n acc + p }, 0.0m, w.ms)",
            "List.sum(List.map(m -> m.price, w.ms))",
    })
    void aStepNamingNothingThatMayStopStopsNone(String total) {
        StopsTheReportSays.Said said = said("Int", total);
        assertEquals(List.of(), stoppingIn(said));
        assertFalse(unreadForAStop(said));
    }
}
