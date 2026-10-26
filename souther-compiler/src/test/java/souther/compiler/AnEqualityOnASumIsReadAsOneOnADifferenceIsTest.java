package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An equality on the sum of two fields is read where the same equality on their difference is:
 * for a fixed field near an end of {@code Int} the other would have to lie outside {@code Int}, and
 * that is the representation running out of partners and no line the model draws. A field held to
 * a narrower run than the other's is a line of the model, and is not passed over.
 */
class AnEqualityOnASumIsReadAsOneOnADifferenceIsTest {

    private static final String NOT_READ = "not read: comparison";

    private static String report(String invariants, String form, String guard) {
        String source = """
                module example.band

                data Low
                data Eq
                data Other

                data Pair = { a: Int, b: Int }%s

                behavior band : (p: Pair) -> Low | Eq | Other

                let band (p) = {
                    let s = %s
                %s
                    Eq
                }
                """.formatted(invariants, form, guard);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(), source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void anEqualityOnASumIsReadLikeOneOnADifference() {
        for (String form : List.of("p.a - p.b", "p.a + p.b")) {
            String report = report("", form, "    guard s == 100 else Other");
            assertFalse(report.contains(NOT_READ), form + "\n" + report);
            assertFalse(report.contains("not accounted for"), form + "\n" + report);
        }
    }

    @Test
    void aLeadingGuardOnTheSumLeavesItRead() {
        for (String form : List.of("p.a - p.b", "p.a + p.b")) {
            String report = report("", form,
                    "    guard s >= 50 else Low\n    guard s == 100 else Other");
            assertFalse(report.contains(NOT_READ), form + "\n" + report);
        }
    }

    @Test
    void aFieldHeldToANarrowerRunThanTheOthersIsALineOfTheModel() {
        String report = report("\n    invariant b >= 0\n    invariant b <= 10", "p.a + p.b",
                "    guard s == 100 else Other");
        assertFalse(report.contains(NOT_READ), report);
        // b is free to take what a needs wherever a stands, and a stands where b can reach it.
        assertTrue(report.contains("rather than dividing the values here, about `p.b`"), report);
        assertFalse(report.contains("rather than dividing the values here, about `p.a`"), report);
    }
}
