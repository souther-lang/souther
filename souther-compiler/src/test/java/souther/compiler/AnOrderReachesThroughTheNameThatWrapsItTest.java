package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A single-value newtype is ordered by the value it wraps (ADR-0047) and an enumeration is ordered
 * by the order its cases are declared in (ADR-0069), so a newtype over an enumeration is ordered by
 * that enumeration. The two rules compose; nothing had to be decided to get this answer, and
 * excepting the enumeration would have been the new decision.
 *
 * <p>It was refused instead, and refused in only some of the places that asked. {@code Carrier}
 * measured a {@code data StageN = Stage} position on {@code Stage}'s declaration order and the
 * specification listed it among the values a line is drawn on, while {@code StageN < StageN} did not
 * typecheck and {@code sort} would not take a list of them — and the generated class, which asked a
 * third way, went out declaring {@code Comparable<StageN>} with a {@code compareTo} that threw
 * {@code IncompatibleClassChangeError} on the first Java reader to compare two (issue #856).
 *
 * <p>What holds the answer in one place now is {@code Ordering}: a witness saying not only that a
 * type has an order but which, built from the newtype spine in one walk. The rows below are the
 * readers that each used to work it out for themselves.
 *
 * <p>The nominal boundary is untouched, and the last rows are what says so. Reaching through the
 * name is what the <em>emission</em> does; admissibility is still asked of the operands as written,
 * so two different newtypes over one enumeration open to the same order and remain uncomparable.
 */
class AnOrderReachesThroughTheNameThatWrapsItTest {

    private static final String STAGES = """
            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won
            data StageN = Stage
            """;

    @Test
    void aComparisonOfTwoWrappedEnumerationsIsTheLineTheBareOneDraws() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                %s
                data In = { stage: StageN }
                data Out = { before: Bool, after: Bool }

                behavior run : (i: In) -> Out constructs Out, StageN

                let run (i) = Out {
                    before = i.stage < StageN(Qualified),
                    after = i.stage >= StageN(Qualified)
                }
                """.formatted(STAGES)), getClass().getClassLoader());

        assertEquals(Map.of("before", true, "after", false), answer(loader, "Prospecting"));
        assertEquals(Map.of("before", false, "after", true), answer(loader, "Qualified"));
        assertEquals(Map.of("before", false, "after", true), answer(loader, "Won"));
    }

    private static Map<?, ?> answer(BytesClassLoader loader, String stage) throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", Map.of("stage", stage));
        Object out = Codecs.apply(
                Emitted.behavior(loader, "demo", "run").getConstructor().newInstance(), in);
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
    }

    @Test
    void theSortFamilyTakesAListOfThem() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort, max, min )

                %s
                data In = { stages: List<StageN> }
                data Out = { sorted: List<StageN>, last: Option<StageN>, first: Option<StageN> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    sorted = sort(i.stages),
                    last = max(i.stages),
                    first = min(i.stages)
                }
                """.formatted(STAGES)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("stages", List.of("Won", "Prospecting", "Qualified")));
        Object out = Codecs.apply(
                Emitted.behavior(loader, "demo", "run").getConstructor().newInstance(), in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(List.of("Prospecting", "Qualified", "Won"), m.get("sorted"));
        assertEquals("Won", m.get("last"));
        assertEquals("Prospecting", m.get("first"));
    }

    @Test
    void aSortByKeyThatIsAWrappedEnumerationOrdersByTheDeclaration() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sortBy )

                %s
                data Deal = { id: String, stage: StageN }
                data In = { deals: List<Deal> }
                data Out = { ids: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    ids = List.map((d) -> d.id, sortBy((d) -> d.stage, i.deals))
                }
                """.formatted(STAGES)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("deals", List.of(
                Map.of("id", "c", "stage", "Won"),
                Map.of("id", "a", "stage", "Prospecting"),
                Map.of("id", "b", "stage", "Qualified"))));
        Object out = Codecs.apply(
                Emitted.behavior(loader, "demo", "run").getConstructor().newInstance(), in);

        assertEquals(List.of("a", "b", "c"),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("ids"));
    }

    @Test
    void theGeneratedClassCompareToAnswersRatherThanThrowing() throws Exception {
        // The claim and what honours it are one answer now. While they were two, the class declared
        // `Comparable<StageN>` and its compareTo asked the case record for a compareTo it does not
        // have — the order is on the sum — so a Java reader putting two in a TreeSet got an
        // IncompatibleClassChangeError. Nothing written in Souther could reach it.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo exposing ( StageN, Stage, Prospecting, Qualified, Won )

                %s
                data Out = { v: Int }

                behavior run : (s: StageN) -> Out constructs Out

                let run (s) = Out { v = 1 }
                """.formatted(STAGES)), getClass().getClassLoader());

        Class<?> stageN = loader.loadClass("demo.StageN");
        assertTrue(Comparable.class.isAssignableFrom(stageN),
                "a newtype over an enumeration is ordered, so its class carries the ordering");

        TreeSet<Object> sorted = new TreeSet<>();
        for (String name : List.of("Won", "Prospecting", "Qualified")) {
            sorted.add(Codecs.decoded(loader, "demo.StageN", name));
        }
        List<Object> names = new java.util.ArrayList<>();
        for (Object v : sorted) {
            names.add(Codecs.encode(loader, "demo.StageN", v));
        }
        assertEquals(List.of("Prospecting", "Qualified", "Won"), names);
    }

    @Test
    void aNewtypeOverANewtypeOverAnEnumerationIsOrderedThroughBoth() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort )

                %s
                data StageNN = StageN
                data In = { stages: List<StageNN> }
                data Out = { sorted: List<StageNN> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.stages) }
                """.formatted(STAGES)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("stages", List.of("Won", "Prospecting", "Qualified")));
        Object out = Codecs.apply(
                Emitted.behavior(loader, "demo", "run").getConstructor().newInstance(), in);

        assertEquals(List.of("Prospecting", "Qualified", "Won"),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("sorted"));
    }

    /**
     * Two sums listing the same three cases in opposite orders. A wrapper takes the order of the sum
     * it names, and the two answers differ — which is what says the order was read off the wrapped
     * declaration and not off the case values, whose places these two sums disagree about.
     */
    @Test
    void aWrapperTakesTheOrderOfTheSumItNamesWhenTwoSumsListTheCases() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort )

                data Alpha
                data Beta
                data Gamma
                data Rising  = Alpha | Beta | Gamma
                data Falling = Gamma | Beta | Alpha
                data RisingN  = Rising
                data FallingN = Falling

                data In = { up: List<RisingN>, down: List<FallingN> }
                data Out = { up: List<RisingN>, down: List<FallingN> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { up = sort(i.up), down = sort(i.down) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of(
                "up", List.of("Gamma", "Alpha", "Beta"),
                "down", List.of("Alpha", "Gamma", "Beta")));
        Object out = Codecs.apply(
                Emitted.behavior(loader, "demo", "run").getConstructor().newInstance(), in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(List.of("Alpha", "Beta", "Gamma"), m.get("up"));
        assertEquals(List.of("Gamma", "Beta", "Alpha"), m.get("down"));
    }

    @Test
    void twoNewtypesOverOneEnumerationDoNotCompare() {
        // The nominal boundary ADR-0047 keeps: these open to one order and are still two types, the
        // way `Amount <= Quantity` is refused though both wrap an Int. A rule that reduced both
        // sides before asking what orders them would admit this.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                %s
                data StageM = Stage
                data Out = { v: Bool }

                behavior run : (a: StageN, b: StageM) -> Out constructs Out

                let run (a, b) = Out { v = a < b }
                """.formatted(STAGES)));

        assertTrue(e.getMessage().contains("StageN") && e.getMessage().contains("StageM"),
                e.getMessage());
    }

    @Test
    void aWrappedEnumerationDoesNotCompareAgainstABareCase() {
        // Only a source literal is taken from the other operand's newtype (ADR-0047), and a case
        // value is a construction and not one. Whether it should be is a decision of its own and is
        // not this one: `x < StageN(Qualified)` is how the comparison is written.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                %s
                data Out = { v: Bool }

                behavior run : (s: StageN) -> Out constructs Out

                let run (s) = Out { v = s < Qualified }
                """.formatted(STAGES)));

        assertTrue(e.getMessage().contains("StageN"), e.getMessage());
    }

    /**
     * The order belongs to the sum, so a case two sums place differently has none of its own, and
     * neither does a name wrapped round it: refused rather than guessed (ADR-0069).
     *
     * <p>The control is the same model with one sum instead of two, and it compiles — so a newtype
     * over a case value is not the shape being refused. What the name carries is whether the value
     * under it has an order, and the second placement is what takes that away.
     */
    @Test
    void aNewtypeOverACaseTwoEnumerationsListHasNoOrder() {
        String model = """
                module demo

                import List ( sort )

                data Alpha
                data Beta
                data Rising  = Alpha | Beta
                %s
                data BetaN = Beta

                data In = { xs: List<BetaN> }
                data Out = { sorted: List<BetaN> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.xs) }
                """;

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(model.formatted("data Falling = Beta | Alpha")));
        assertTrue(e.getMessage().contains("BetaN"), e.getMessage());

        // The control: one sum listing the case, everything else the same. What the refusal is about
        // is the second placement and not the shape of a newtype over a case value.
        assertDoesNotThrow(() -> Compiler.compile(model.formatted("")));
    }
}
