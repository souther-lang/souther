package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.CoverageObligation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The other producer of the same claim, held to the same reading of it.
 *
 * <p>A clause of an {@code ensures} states a comparison the way a body's condition does, so what it
 * places and what it places it about are read the same way. Fixed here as well as for a guard because
 * two producers of one classification are how the classification stops being one.
 */
class AnEnsuresBetweenTwoPositionsSinglesNothingOutTest {

    private static Set<CoverageObligation> raisedBy(String clause) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { a: Int, other: Int }
                data Ok
                data No

                behavior f : (r: R) -> Ok | No
                    ensures No -> %s
                let f (r) = No

                example f
                    | "one" : (R { a = 1, other = 2 }) -> No
                """.formatted(clause), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence partition = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().get(0).partition();
        Set<CoverageObligation> out = new LinkedHashSet<>();
        partition.unanswered().forEach(each -> out.add(each.question()));
        return out;
    }

    /** A rule about a pair singles nothing out at either of them. */
    @Test
    void anEqualityBetweenTwoPositionsRaisesNothingAboutOne() {
        assertEquals(Set.of(), raisedBy("r.a == r.other"));
        assertEquals(Set.of(), raisedBy("r.a /= r.other"));
    }

    /** While one about a single position still asks what it asks. */
    @Test
    void andOneAboutASinglePositionStillDoes() {
        assertEquals(Set.of(CoverageObligation.SINGLETON, CoverageObligation.PARTITION),
                raisedBy("r.a == Int.min(20, 30)"));
    }
}
