package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position that could not be read is one behavior's problem.
 *
 * <p>A reason larger than a behavior — a source that was not evaluated, a module whose classes were
 * not made — is missing rows for whatever it held, so it counts against every behavior in it. A
 * position is not larger than a behavior. It is a place inside one behavior's input, and marking the
 * rest of the module partial over a value read there says their measures could not be made when they
 * could.
 *
 * <p>This has never been asked before. Nothing wrote a position into the list a report reads, so the
 * fallback — anything not a behavior is everything — answered for it and was never wrong out loud.
 */
class AReasonAboutAPositionCountsOnlyAgainstItsBehaviorTest {

    /** One behavior whose row writes more than an observation keeps, and one whose rows are read. */
    private static String source() {
        StringBuilder inner = new StringBuilder();
        for (int i = 0; i < 64; i++) {
            inner.append(i == 0 ? "" : ", ")
                    .append("Item { a = \"").append(i).append("\", b = \"").append(i)
                    .append("\", c = \"").append(i).append("\" }");
        }
        StringBuilder groups = new StringBuilder();
        for (int i = 0; i < 64; i++) {
            groups.append(i == 0 ? "" : ", ").append("Group { items = [ ").append(inner).append(" ] }");
        }
        return """
                module example.split

                data Yes
                data No
                data Flag = Yes | No

                data Item = { a: String, b: String, c: String }
                data Group = { items: List<Item> }

                data Draft = { groups: List<Group>, flag: Flag }
                data Small = { flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) = Ok { n = 0 }

                behavior cancel : (request: Small) -> Ok
                    constructs Ok

                let cancel (request) = Ok { n = 1 }

                example take
                    | (Draft { groups = [ %s ], flag = Yes }) -> Ok { n = 0 }

                example cancel
                    | (Small { flag = Yes }) -> Ok { n = 1 }
                    | (Small { flag = No }) -> Ok { n = 1 }
                """.formatted(groups);
    }

    private static AdequacyReport report() {
        return AdequacyReport.of(compilationOf());
    }

    @Test
    void theReasonNamesTheBehaviorThePositionIsIn() {
        List<Incompleteness> why = report().modules().get(0).incompleteness();

        assertFalse(why.isEmpty(), "the position that could not be read is said");
        assertTrue(why.stream().allMatch(gap -> gap.behavior().equals(Optional.of("take"))),
                why.toString());
        assertTrue(why.stream().anyMatch(gap -> gap.countsAgainst("take")));
        assertFalse(why.stream().anyMatch(gap -> gap.countsAgainst("cancel")),
                "a position of `take` is not a reason about `cancel`");
    }

    /** And the behavior beside it keeps its answers. */
    @Test
    void theOtherBehaviorIsNotMadePartialByIt() {
        AdequacyReport report = report();

        assertEquals(MeasurementStatus.PARTIAL, behavior(report, "take").status());
        assertEquals(MeasurementStatus.COMPLETE, behavior(report, "cancel").status());
    }

    /** Filtering to it drops the reason with it, so the module view is complete for that reader. */
    @Test
    void filteringToItDropsAReasonAboutAnotherBehaviorsPosition() {
        AdequacyReport only = AdequacyReport.of(compilationOf()).only(null, "cancel");

        assertEquals(List.of(), only.modules().get(0).incompleteness());
        assertEquals(MeasurementStatus.COMPLETE, only.status());
    }

    private static Compilation compilationOf() {
        Compilation compilation = Compilation.ofSource(source(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static AdequacyReport.BehaviorReport behavior(AdequacyReport report, String name) {
        return report.modules().get(0).behaviors().stream()
                .filter(each -> each.name().equals(name)).findFirst().orElseThrow();
    }
}
