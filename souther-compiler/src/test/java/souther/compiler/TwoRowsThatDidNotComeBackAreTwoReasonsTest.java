package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two rows that did not come back are two things to go and look at.
 *
 * <p>A reason a measure could not read everything is kept one per identity — a module's classes
 * failing to be instrumented is one fact however many sources went looking for it — and a row that
 * did not come back used to be identified by the behavior it is written for. So a behavior with two
 * such rows left one reason, and the report said "a row of `take` did not come back" once whichever
 * of them a reader was owed.
 *
 * <p>The other half is the source. A row written with no name is numbered within the source it is
 * written in, so a behavior exampled in its module and in an attached file has a first row in each;
 * carried as the ordinal alone, those two are one identity in a set (issue #996).
 */
class TwoRowsThatDidNotComeBackAreTwoReasonsTest {

    private static List<Incompleteness> reasonsOf(Compilation compilation, String module) {
        for (AdequacyReport.ModuleReport each : AdequacyReport.of(compilation).modules()) {
            if (each.module().equals(module)) {
                return each.incompleteness();
            }
        }
        throw new AssertionError("no module called " + module);
    }

    private static Compilation overrunning(List<String> sources, String target) {
        Compilation compilation = Compilation.ofSources(sources,
                souther.compiler.meta.ModulePath.EMPTY);
        compilation.withDeadline(DoesNotComeBack.overrunningOn(
                DoesNotComeBack.everythingAboutRowsOf(target)));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** Two rows of one behavior, in one source. */
    @Test
    void twoRowsOfOneBehaviorLeaveTwoReasons() {
        Compilation compilation = overrunning(List.of("""
                module example.pair

                data Draft = { n: Int }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) = Ok { n = request.n }

                example take
                    | (Draft { n = 1 }) -> Ok { n = 1 }
                    | (Draft { n = 2 }) -> Ok { n = 2 }
                """), "take");

        assertEquals(List.of("take/0/#1", "take/0/#2"),
                reasonsOf(compilation, "example.pair").stream()
                        .filter(gap -> gap.scope() == Incompleteness.Scope.ROW)
                        .map(Incompleteness::subject).toList(),
                "each row is its own reason, and says which row it is");
    }

    /**
     * And one row apiece in two sources, both of them the first of their source.
     *
     * <p>The case the ordinal alone cannot tell apart. Both are {@code #1}; what makes them two is
     * the source, which is why a row's identity carries it.
     */
    @Test
    void aFirstRowInEachOfTwoSourcesAreTwoReasons() {
        Compilation compilation = overrunning(List.of("""
                module example.across

                data Draft = { n: Int }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) = Ok { n = request.n }

                example take
                    | (Draft { n = 1 }) -> Ok { n = 1 }
                """, """
                examples for example.across

                example take
                    | (Draft { n = 2 }) -> Ok { n = 2 }
                """), "take");

        assertEquals(List.of("take/0/#1", "take/1/#1"),
                reasonsOf(compilation, "example.across").stream()
                        .filter(gap -> gap.scope() == Incompleteness.Scope.ROW)
                        .map(Incompleteness::subject).toList(),
                "the first row of each source is a row of its own");
    }
}
