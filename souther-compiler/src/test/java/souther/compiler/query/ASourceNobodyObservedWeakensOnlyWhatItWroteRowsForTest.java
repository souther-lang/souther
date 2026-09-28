package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Incompleteness;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A source nothing was observed from weakens the behaviors whose rows it holds, and no others.
 *
 * <p>Which rows a source holds is what a source-wide reason claims could not be read. Where the
 * module was prepared, they were read: the blocks written in that source are there, each naming the
 * behavior it is of, and every row in them is already listed as a row nothing came back for. A
 * reason at the scope of the source, added beside that, hands the same absence to behaviors that
 * wrote nothing in it — and a behavior exampled only in a source that was observed is told its rows
 * may cover anything.
 */
class ASourceNobodyObservedWeakensOnlyWhatItWroteRowsForTest {

    /**
     * Two behaviors, each exampled in this source. The attached file below examples only one of
     * them, so the other's rows are written where nothing went wrong.
     */
    private static final String MODULE = """
            module example.split

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Draft = { cost: Amount }
            data Ok = { n: Int }

            let shared = Draft { cost = Amount(7) }

            behavior take : (request: Draft) -> Ok
                constructs Ok

            let take (request) = Ok { n = request.cost.value }

            behavior keep : (request: Draft) -> Ok
                constructs Ok

            let keep (request) = Ok { n = request.cost.value }

            example take
                | (Draft { cost = Amount(7) }) -> Ok { n = 7 }

            example keep
                | (Draft { cost = Amount(7) }) -> Ok { n = 7 }
            """;

    /** It declares a value the module already declares, so its rows are never evaluated. */
    private static final String ATTACHED = """
            examples for example.split

            let shared = Draft { cost = Amount(0) }

            example take
                | (Draft { cost = Amount(0) }) -> Ok { n = 0 }
            """;

    /** The same file, writing two rows for the one behavior instead of one. */
    private static final String TWO_MORE_ROWS = """
            examples for example.split

            let shared = Draft { cost = Amount(0) }

            example take
                | (Draft { cost = Amount(0) }) -> Ok { n = 0 }
                | (Draft { cost = Amount(1) }) -> Ok { n = 1 }
            """;

    @Test
    void aBehaviorThatWroteNoRowsInTheUnobservedSourceIsNotWeakenedByIt() {
        AdequacyReport.ModuleReport module = report();

        Set<Incompleteness.Code> keep = codesAgainst(module, "keep");

        assertEquals(Set.of(), keep,
                "`keep` is exampled only in a source that was observed");
    }

    @Test
    void andTheOneThatWroteRowsInItIsToldSo() {
        AdequacyReport.ModuleReport module = report();

        Set<Incompleteness.Code> take = codesAgainst(module, "take");

        assertTrue(take.contains(Incompleteness.Code.OBSERVATION_ABSENT),
                () -> "`take` wrote rows in the source nothing came back from: " + take);
    }

    /** And the reason it is told is about the row that was not read, which says whose it is. */
    @Test
    void andTheReasonIsAboutTheRowThatWasNotRead() {
        AdequacyReport.ModuleReport module = report();

        List<Incompleteness.Fact> absent = absent(module);

        assertEquals(1, absent.size(), absent::toString);
        assertEquals(Incompleteness.Scope.ROW, absent.get(0).scope());
        assertEquals("take", absent.get(0).behavior().orElseThrow(),
                "whose measurement it counts against");
    }

    /**
     * And two rows of one behavior that were not read are two of them.
     *
     * <p>The attached file writes a second row for the same behavior. Said of anything larger than
     * a row, both would arrive under one identity and a reader would be told to go and look at one
     * of the two places.
     */
    @Test
    void andTwoRowsOfOneBehaviorThatWereNotReadAreTwoReasons() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE, TWO_MORE_ROWS),
                ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        List<Incompleteness.Fact> absent = absent(AdequacyReport.of(compilation).modules().get(0));

        assertEquals(2, absent.size(), absent::toString);
    }

    private static List<Incompleteness.Fact> absent(AdequacyReport.ModuleReport module) {
        return module.weakenedBy().observationCauses().stream()
                .map(Incompleteness.Met::fact)
                .filter(fact -> fact.code() == Incompleteness.Code.OBSERVATION_ABSENT)
                .toList();
    }

    private static Set<Incompleteness.Code> codesAgainst(AdequacyReport.ModuleReport module,
                                                         String behavior) {
        return module.behaviors().stream()
                .filter(each -> each.name().equals(behavior))
                .flatMap(each -> each.weakenedBy().observationCauses().stream())
                .map(met -> met.fact().code())
                .collect(Collectors.toCollection(java.util.LinkedHashSet::new));
    }

    private static AdequacyReport.ModuleReport report() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE, ATTACHED),
                ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().get(0);
    }
}
