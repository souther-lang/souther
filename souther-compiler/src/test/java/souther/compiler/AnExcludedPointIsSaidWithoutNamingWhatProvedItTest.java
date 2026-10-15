package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point no value can stand at is said as that, whatever showed it.
 *
 * <p>A {@code Set<Bool>} holds each of two values once, so a count of it past two has no value and
 * no rule is written about it. An author told that the rules refuse such a point goes looking for
 * a rule and finds none. The same words are said where an invariant is what leaves the point
 * empty, because what a reader does about the point is the same either way.
 */
class AnExcludedPointIsSaidWithoutNamingWhatProvedItTest {

    /** Nothing but the element's two values leaves the points past two empty. */
    private static final String BY_THE_TYPE = """
            module example.sets
            data Low
            data High

            behavior pick : (xs: Set<Bool>) -> Low | High
            let pick (xs) = if Set.size(xs) >= 3 then High else Low
            """;

    /** An invariant on the set is what leaves the points past one empty. */
    private static final String BY_A_RULE = """
            module example.sets
            data Low
            data High
            data Few = Set<Bool>
              invariant Set.size(value) <= 1

            behavior pick : (xs: Few) -> Low | High
            let pick (xs) = if Set.size(xs.value) >= 2 then High else Low
            """;

    private static final String GUARDED = """
            module example.sets
            behavior pick : (xs: Set<Bool>) -> Int
            let pick (xs) = {
                guard Set.size(xs) >= 3 else 0

                1
            }
            """;

    @Test
    void aPointPastWhatTheElementHasValuesForIsExcludedInTheSameWordsAsOneAnInvariantRefuses() {
        for (String model : List.of(BY_THE_TYPE, BY_A_RULE)) {
            String page = report(measured(model));

            assertTrue(page.lines().anyMatch(line -> line.contains("excluded — no value can stand"
                            + " there")),
                    () -> "the points past the end are excluded: " + page);
            assertTrue(page.lines().filter(line -> line.contains("excluded"))
                            .noneMatch(line -> line.contains("rule")),
                    () -> "what showed it is not named: " + page);
        }
    }

    @Test
    void aWayPastAGuardNoValueTakesIsSaidWithoutNamingWhatProvedIt() {
        String block = block(measured(GUARDED));

        assertTrue(block.contains("no value can go that way, so no row goes this way"),
                () -> "the way past the guard is one no row goes: " + block);
        assertTrue(block.lines().filter(line -> line.contains("no row goes this way"))
                        .noneMatch(line -> line.contains("rule")),
                () -> "what showed it is not named: " + block);
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String block(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.sets")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }
}
