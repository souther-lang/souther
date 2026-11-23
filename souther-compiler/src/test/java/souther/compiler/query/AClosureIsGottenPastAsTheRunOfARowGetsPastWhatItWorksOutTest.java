package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a closure handed to an operation of the library works out is gotten past as the run of a
 * row gets past anything else: a behavior it calls is gotten past where every row of that behavior
 * gets past its body, an {@code unreachable} in that body included. So a body that walks a list
 * through such a closure is not left open on the call.
 */
class AClosureIsGottenPastAsTheRunOfARowGetsPastWhatItWorksOutTest {

    private static final String COMPLETE = "measurement: complete";

    /** Measured at {@link Adequacy.Level#OFF}: whether what a rule states is read, and whether a
     *  stop is resolved, is what the rules say, and asks nothing of the rows. */
    private static String reportOf(String model) {
        Compilation compilation = ACompiledModel.measured("module m\n" + model,
                Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        return AdequacyReport.of(compilation).only(null, "enough")
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** A body asking whether every element of a list, as {@code closure} tests it, holds. */
    private static final String EVERY = """
            behavior enough : (xs: List<Int>) -> Bool

            let enough (xs) = List.all(x -> %s, xs)

            example enough
                | "all" : ([4, 6]) -> true
                | "one short" : ([4, 2]) -> false
            %s""";

    /** The element itself: nothing in the closure may end a run, and the walk is read to the end.
     *  What the one below is measured against. */
    @Test
    void aClosureWorkingOutNothingThatMayEndARunIsReadToTheEnd() {
        String report = reportOf(EVERY.formatted("x >= 3", ""));
        assertTrue(report.contains(COMPLETE), report);
    }

    @Test
    void aBehaviorAClosureCallsIsGottenPastWhereItsRowsAre() {
        String report = reportOf(EVERY.formatted("counted(x) >= 3", """

                behavior counted : (n: Int) -> Int

                let counted (n) = if n >= 0 then n else unreachable "a count is never below nought"

                example counted
                    | "four" : (4) -> 4
                """));
        assertTrue(report.contains(COMPLETE), report);
        assertFalse(report.contains("a run may stop at the call of counted"), report);
    }
}
