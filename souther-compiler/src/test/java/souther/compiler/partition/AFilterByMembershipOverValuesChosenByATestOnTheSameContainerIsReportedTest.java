package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A filter by a container's membership, over values each chosen by a test that reads the same
 * container beside another comparison, is reported whatever it comes to: the statement of the
 * filter holds a quantifier over the container, and the part the choice leaves that no one value
 * stands for is put where it stands, never the statement that holds it.
 */
class AFilterByMembershipOverValuesChosenByATestOnTheSameContainerIsReportedTest {

    @Test
    void theFormOfAnyIsReported() {
        assertReported("""
                module h7

                behavior f : (hs: List<Int>, ns: List<Int>) -> List<Int>
                let f (hs, ns) =
                    ns
                        |> List.map(n -> if n >= 1 && Bool.not(List.any(k -> k == n, hs)) then n else n + 1)
                        |> List.filter(d -> List.any(h -> h == d, hs))
                """);
    }

    @Test
    void theFormOfAMembershipIsReported() {
        assertReported("""
                module h7

                behavior f : (hs: Set<Int>, ns: List<Int>) -> List<Int>
                let f (hs, ns) =
                    ns
                        |> List.map(n -> if n >= 1 && Set.contains(n, hs) then n else n + 1)
                        |> List.filter(d -> Set.contains(d, hs))
                """);
    }

    @Test
    void theChoiceByAFindIsReported() {
        assertReported("""
                module h7

                behavior f : (hs: Set<Int>, ns: List<Int>) -> List<Int>
                let f (hs, ns) =
                    ns
                        |> List.map(n -> [ n, n + 1 ]
                                |> List.find(x -> Int.floorMod(x, 7) >= 1 && Bool.not(Set.contains(x, hs)))
                                |> Option.withDefault(n))
                        |> List.filter(d -> Set.contains(d, hs))
                """);
    }

    private static void assertReported(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        String report = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        assertFalse(report.isEmpty());
    }
}
