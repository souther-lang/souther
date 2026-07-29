package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A sum every one of whose cases is a unit data is ordered by the order its cases are declared —
 * the order a deal moves through its stages, which nothing else in the model carries. This is what
 * F# gives a discriminated union, Haskell a derived {@code Ord}, Rust a derived {@code Ord} over
 * variants, and Java an enum's ordinal; Elm is the one language that withholds it, and withholding
 * it is why a report has to project the cases onto {@code Int} by hand (issue #161).
 */
class CompileEnumerationOrderTest {

    private Object run(String src, String outType) throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("n", 1L));
        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        return Codecs.encode(loader, outType, Codecs.apply(behavior, in));
    }

    @Test
    void sortOrdersTheCasesAsDeclared() throws Exception {
        String src = """
                module demo

                data Stage = Prospecting | Negotiation | Won | Lost
                data In = { n: Int }
                data Out = { stages: List<Stage> }

                behavior run : (i: In) -> Out constructs Out, Prospecting, Won, Lost

                let run (i) = Out { stages = List.sort([ Lost, Won, Prospecting ]) }
                """;

        assertEquals(Map.of("stages", List.of("Prospecting", "Won", "Lost")), run(src, "demo.Out"));
    }

    @Test
    void anEarlierCaseIsLessThanALaterOne() throws Exception {
        String src = """
                module demo

                data Stage = Prospecting | Negotiation | Won | Lost
                data In = { n: Int }
                data Out = { early: Bool, late: Bool }

                behavior run : (i: In) -> Out constructs Out, Prospecting, Won

                let run (i) = Out { early = Prospecting < Won, late = Won < Prospecting }
                """;

        assertEquals(Map.of("early", true, "late", false), run(src, "demo.Out"));
    }

    /**
     * A unit data may be a case of two sums, which place it differently, so the case value alone
     * carries no order. The sum being compared against says which order applies.
     */
    @Test
    void aCaseSharedByTwoEnumerationsIsOrderedByTheSumItIsComparedWith() throws Exception {
        String src = """
                module demo

                data Stage = Prospecting | Won
                data Terminal = Won | Prospecting
                data In = { n: Int }
                data Out = { early: Bool }

                behavior run : (i: In) -> Out constructs Out, Prospecting, Won

                let run (i) = {
                    let s: Stage = Prospecting
                    Out { early = s < Won }
                }
                """;

        assertEquals(Map.of("early", true), run(src, "demo.Out"));
    }

    @Test
    void sortByOrdersRowsOnTheirStage() throws Exception {
        String src = """
                module demo

                data Stage = Prospecting | Negotiation | Won | Lost
                data Deal = { stage: Stage }
                data In = { n: Int }
                data Out = { deals: List<Deal> }

                behavior run : (i: In) -> Out constructs Out, Deal, Won, Negotiation, Prospecting

                let run (i) =
                    Out { deals = List.sortBy(d -> d.stage,
                            [ Deal { stage = Won }, Deal { stage = Prospecting },
                              Deal { stage = Negotiation } ]) }
                """;

        assertEquals(Map.of("deals", List.of(
                        Map.of("stage", "Prospecting"),
                        Map.of("stage", "Negotiation"),
                        Map.of("stage", "Won"))),
                run(src, "demo.Out"));
    }
}
