package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.CoverageObligation;
import souther.compiler.check.RuleCitation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison is written rather than named, so the question it raises is cited by where it is.
 *
 * <p>{@code RuleRef.named} says a guard's rule is never rendered to a reader on its own: there is
 * nothing the author called it, and "the comparison" sends them nowhere. An invariant's clause has a
 * name and is found by it. One string over both would have to spell a place as a name, which is the
 * assumption a report carrying only names was making before a producer without one reached it.
 *
 * <p>Not the reading occurrence either. Where a rule was read is the partition's, and one comparison
 * inside a helper is read once per call — a question the model raised once would then have to pick
 * one of them to show. This is where the author wrote it, which is one however often it is read.
 */
class AGuardsQuestionIsCitedByWhereItIsWrittenTest {

    /** A comparison stating a line at 20 that this compiler cannot fold, beside a bound it can. */
    private static final String MODEL = """
            module example.repro

            data Length = Int
                invariant min = value >= 1

            behavior price : (length: Length) -> Int
            let price (length) =
                if length.value <= Int.min(20, 30) then 1 else 2

            example price
                | "one" : (Length(1)) -> 1
            """;

    private static PartitionEvidence partition() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().get(0).behaviors().get(0).partition();
    }

    /** The comparison raises both questions its line raises, and nothing answers either. */
    @Test
    void aComparisonNothingCouldReadLeavesBothOfItsQuestionsStanding() {
        List<PartitionEvidence.Unanswered> standing = partition().unanswered().stream()
                .filter(each -> each.cited() instanceof RuleCitation.WrittenAt)
                .toList();

        assertEquals(Set.of(CoverageObligation.BOUNDARY, CoverageObligation.PARTITION),
                standing.stream().map(PartitionEvidence.Unanswered::question)
                        .collect(java.util.stream.Collectors.toSet()),
                () -> "one line, two questions: " + standing);
    }

    /** And it is cited by where the author wrote it, not by a name it does not have and not by
     *  the construct standing round it. */
    @Test
    void itIsCitedByThePlaceAndNamedByNothing() {
        PartitionEvidence.Unanswered one = partition().unanswered().stream()
                .filter(each -> each.question() == CoverageObligation.BOUNDARY)
                .findFirst().orElseThrow();

        RuleCitation.WrittenAt written =
                assertInstanceOf(RuleCitation.WrittenAt.class, one.cited());
        assertTrue(written.said(SourceNameResolver.identity(), null).startsWith("comparison@"),
                () -> "what the rule is and where it is written: "
                        + written.said(SourceNameResolver.identity(), null));
    }

    /** The invariant beside it keeps its name, which is the other half of the same rule. */
    @Test
    void anInvariantIsStillCitedByTheNameTheAuthorGaveIt() {
        Compilation compilation = Compilation.ofSource("""
                module example.repro

                data Length = Int
                    invariant square = value * value >= 4

                behavior price : (length: Length) -> Int
                let price (length) = if length.value >= 5 then 1 else 2

                example price
                    | "one" : (Length(5)) -> 1
                """, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        PartitionEvidence evidence = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().get(0).partition();

        RuleCitation.Named named = assertInstanceOf(RuleCitation.Named.class,
                evidence.unanswered().get(0).cited());
        assertEquals("invariant Length (square)", named.name());
    }
}
