package souther.compiler.partition;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A walk of decimals stops a run nowhere of its own, and a step that adds a part of the element
 * works out nothing else on the way to its answer. What it gives a name before that is worked out
 * whether or not anything reads it: a product of two whole numbers there may pass an {@code Int},
 * and a run that gets there stops. The same walk with nothing named stops none.
 */
class WhatAStepOfDecimalsNamesIsAskedWhetherItStopsARunTest {

    private static final String SOURCE = """
            module d

            data M = { a: Int, b: Int, price: Decimal }
            data W = { ms: List<M> }

            behavior f : (w: W) -> Int

            let f (w) = {
                let t = %s
                if t >= 10.0m then 1 else 0
            }
            """;

    /** The lines that say a run may stop, or that a comparison is not read. */
    private static List<String> stopsAndUnread(String total) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(total), "Main");
        // The readings of the walk, and no row looked for, which nothing here asks about.
        compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("· stop") || line.contains("not read:"))
                .toList();
    }

    @ParameterizedTest
    @ValueSource(strings = {
            "List.fold((acc, m) -> { let n = m.a * m.b \n acc + m.price }, 0.0m, w.ms)",
            "List.sum(List.map(m -> { let n = m.a * m.b \n m.price }, w.ms))",
    })
    void aWholeNumberAStepNamesIsAsked(String total) {
        assertFalse(stopsAndUnread(total).isEmpty());
    }

    @ParameterizedTest
    @ValueSource(strings = {
            "List.fold((acc, m) -> acc + m.price, 0.0m, w.ms)",
            "List.fold((acc, m) -> { let p = m.price \n acc + p }, 0.0m, w.ms)",
            "List.sum(List.map(m -> m.price, w.ms))",
    })
    void aStepNamingNothingThatMayStopStopsNone(String total) {
        assertEquals(List.of(), stopsAndUnread(total));
    }
}
