package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Output;
import souther.compiler.source.SourceId;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A product of two forms no one number holds at a value is a number no row writes, so it has no
 * target, and a search over it says it was not shown to be reached rather than stopping the run.
 */
class AProductNoOneNumberHoldsIsNoTargetAndIsNotClaimedReachedTest {

    private static NumericTerm number(String name) {
        return new NumericTerm.ValueOf(TermPath.of(name));
    }

    private static LinearForm<NumericTerm> sumOf(String first, String second) {
        return new LinearForm<>(ExactRatio.ZERO,
                Map.of(number(first), ExactRatio.ONE, number(second), ExactRatio.ONE));
    }

    /** {@code (a + b) * rate}: neither factor is a number alone beside a form of one number. */
    @Test
    void aSumTimesANumberHasNoWayAndNoTarget() {
        NumericTerm.ProductOf product = NumericTerm.ProductOf.of(sumOf("a", "b"),
                LinearForm.atom(number("rate")));
        assertNull(product.atAValue());
        assertEquals(Optional.empty(), RealizationTarget.of(product));
    }

    /** {@code (a + b) * (rate + r2)}. */
    @Test
    void aSumTimesASumHasNoWayAndNoTarget() {
        NumericTerm.ProductOf product = NumericTerm.ProductOf.of(sumOf("a", "b"),
                sumOf("rate", "r2"));
        assertNull(product.atAValue());
        assertEquals(Optional.empty(), RealizationTarget.of(product));
    }

    /** A product that has a way keeps the root of the number that carries it. */
    @Test
    void aProductWithAWayKeepsTheRootOfItsCarrier() {
        NumericTerm.ProductOf product = NumericTerm.ProductOf.of(LinearForm.atom(number("a")),
                LinearForm.atom(number("rate")));
        NumericTerm.ProductOf.AtAValue way = product.atAValue();
        assertNotNull(way);
        RealizationTarget.OfANumber target = RealizationTarget.of(product).orElseThrow();
        assertEquals(RealizationTarget.ofAPlace((NumericTerm.FromOnePosition) way.carrier())
                .writeRoot(), target.writeRoot());
    }

    /** A target of a product cannot be made without the number that carries it. */
    @Test
    void aProductTargetIsNotMadeBesideAnotherCarrierOrNone() {
        NumericTerm.ProductOf withAWay = NumericTerm.ProductOf.of(
                LinearForm.atom(number("a")), LinearForm.atom(number("rate")));
        NumericTerm.ProductOf withNone = NumericTerm.ProductOf.of(sumOf("a", "b"),
                LinearForm.atom(number("rate")));
        RealizationTarget.OfANumber other = RealizationTarget.ofAPlace(
                (NumericTerm.FromOnePosition) number("elsewhere"));
        assertThrows(IllegalArgumentException.class,
                () -> new RealizationTarget.OfAProduct(withAWay, other, other));
        assertThrows(IllegalArgumentException.class,
                () -> new RealizationTarget.OfAProduct(withNone, other, other));
    }

    /**
     * The reproduction as the issue gives it, examples included: the two rows run and are
     * answered as written, and the measuring that goes beside them does not stop the run.
     */
    @Test
    void theExamplesOfTheReproductionRunAndAreAnswered() {
        String model = modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.multiply(Decimal.add(a, b), rate)") + """

                example plan
                    | "a" : (100.0m, 200.0m, 346.0m, 0.1m) -> Out { within = true }
                    | "b" : (100.0m, 4000.0m, 346.0m, 0.1m) -> Out { within = false }
                """;
        Compilation compilation = Compilation.ofSources(List.of(model), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        List<RowOutcome> rows = new ArrayList<>();
        for (String module : compilation.modules()) {
            for (SourceId id : compilation.exampleSourcesOf(module)) {
                Output.Examples.Of ran = compilation.db()
                        .ask(Output.Examples.asked(compilation.db(), module, id)).value();
                if (ran != null) {
                    rows.addAll(ran.rows());
                }
            }
        }
        assertEquals(List.of("a", "b"),
                rows.stream().map(row -> row.identity().shown()).sorted().toList(), rows.toString());
        for (RowOutcome row : rows) {
            assertTrue(row.answered(), row.toString());
        }
    }

    /** Every target the factory makes answers its root, whatever kind of term it was made for. */
    @Test
    void everyTargetTheFactoryMakesHasARoot() {
        List<NumericTerm> terms = List.of(number("a"),
                NumericTerm.ProductOf.of(LinearForm.atom(number("a")),
                        LinearForm.atom(number("rate"))),
                NumericTerm.ProductOf.of(sumOf("a", "b"), LinearForm.atom(number("rate"))));
        for (NumericTerm term : terms) {
            RealizationTarget.of(term).ifPresent(target ->
                    assertNotNull(assertDoesNotThrow(target::writeRoot), term.toString()));
        }
    }

    private static String modelOf(String parameters, String net) {
        return """
                module t.m4 exposing ( Out, plan )

                data Out = { within: Bool }

                behavior plan : (%s) -> Out

                let plan (%s) = {
                    let net = %s
                    Out { within = Decimal.compare(net, limit) <= 0 }
                }
                """.formatted(parameters, parameters.replaceAll(":\\s*[A-Za-z]+", ""), net);
    }

    /**
     * The model measures, and no row is said to stand where no value can: a relation over a
     * product no row is written for is one not shown to be reached.
     */
    private static void assertMeasured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        assertDoesNotThrow(() -> {
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
        }, model);
        ACompiledModel.compiles(compilation);
        assertNotNull(Adequacy.readingsOf(compilation.db(), "t.m4"), model);
        assertTrue(compilation.db().ask(new Adequacy.Coverage("t.m4")).value()
                .containsKey("plan"), model);
    }

    /** The reproduction, its two-sum form and its whole-number form measure. */
    @Test
    void aRelationOverAProductNoOneNumberHoldsIsMeasuredWithoutAnInternalError() {
        assertMeasured(modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.multiply(Decimal.add(a, b), rate)"));
        assertMeasured(modelOf(
                "a: Decimal, b: Decimal, limit: Decimal, rate: Decimal, r2: Decimal",
                "Decimal.multiply(Decimal.add(a, b), Decimal.add(rate, r2))"));
        assertMeasured(modelOf("a: Int, b: Int, c: Int, limit: Decimal",
                "Decimal.fromInt((a + b) * c)"));
    }

    /**
     * A line on the product is still owed its points, and none is said to be one nothing can be
     * written at: each is left unresolved, which is what a point not shown to be reached is.
     */
    @Test
    void thePointsOfALineOnTheProductAreOwedAndLeftUnresolved() {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (a: Int, b: Int, c: Int) -> Ok | No
                let f (a, b, c) = {
                    guard (a + b) * c >= 1000 else No
                    Ok
                }
                """;
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "demo").get("f");
        List<BorderAssessment> product = lines.stream()
                .filter(each -> each.axis().contains("(a + b) * c")).toList();
        assertEquals(1, product.size(), lines.toString());
        for (ItemAssessment item : product.get(0).items().values()) {
            ItemAssessment.Owed owed = assertInstanceOf(ItemAssessment.Owed.class, item);
            assertTrue(!owed.searches().each().isEmpty());
            for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                ItemAssessment.Attempt.Unresolved unresolved =
                        assertInstanceOf(ItemAssessment.Attempt.Unresolved.class, attempt);
                assertTrue(unresolved.uncomposed().onTheWay().stream().noneMatch(
                        ReachabilityGap.ProvedImpossible.class::isInstance));
            }
        }
    }

    /**
     * The same product put to every reader of a number a row search has: beside a number in a
     * form, under a remainder, against another number, beside a condition on one factor, and as
     * a factor of another product.
     */
    @Test
    void aProductNoOneNumberHoldsIsMeasuredWhateverItIsPutBesideOrUnder() {
        for (String condition : List.of(
                "(a + b) * c >= 1000",
                "(a + b) * c + d >= 1000",
                "Int.floorMod((a + b) * c, 7) >= 1",
                "(a + b) * c >= d",
                "(a + b) * c >= 1000 && a >= 5",
                "(a + b) * c >= 1000 && (a + b) * c <= 5000",
                "d * ((a + b) * c) >= 1000")) {
            String model = """
                    module demo

                    data Ok
                    data No

                    behavior f : (a: Int, b: Int, c: Int, d: Int) -> Ok | No
                    let f (a, b, c, d) = {
                        guard %s else No
                        Ok
                    }
                    """.formatted(condition);
            Compilation compilation = Compilation.ofSource(model, "Main");
            assertDoesNotThrow(() -> {
                compilation.measure(Adequacy.Asked.fullReport());
                compilation.answerEverything();
            }, condition);
            ACompiledModel.compiles(compilation);
            assertNotNull(Adequacy.readingsOf(compilation.db(), "demo"), condition);
            assertNotNull(compilation.db().ask(new Adequacy.Coverage("demo")).value(), condition);
        }
    }

    /**
     * The same product beside what a list adds up to, how many elements meet a statement that
     * reads it, and a total of products taken over the elements.
     */
    @Test
    void aProductNoOneNumberHoldsIsMeasuredBesideAListsTotalsAndCounts() {
        for (String condition : List.of(
                "List.sum(ns) + (a + b) * c >= 1000",
                "List.length(List.filter(n -> n * c >= 10, ns)) >= 2",
                "List.length(List.filter(n -> (n + a) * c >= 10, ns)) >= 2",
                "List.sum(List.map(n -> n * c, ns)) >= 100",
                "List.sum(List.map(n -> (n + a) * c, ns)) >= 100",
                "List.sum(ns) >= 9 && (a + b) * c >= 1000",
                "List.length(List.filter(n -> (n + a) * c >= 10, ns)) >= 2 && a >= 5",
                "a >= 5 && List.length(List.filter(n -> (n + a) * c >= 10, ns)) >= 2",
                "List.length(List.filter(n -> (n + a) * c >= 10, ns)) >= 2 && List.sum(ns) >= 9",
                "List.length(List.filter(n -> (n + a) * c >= 10, ns)) >= 1 && c >= 3")) {
            String model = """
                    module demo

                    data Ok
                    data No

                    behavior f : (ns: List<Int>, a: Int, b: Int, c: Int) -> Ok | No
                    let f (ns, a, b, c) = {
                        guard %s else No
                        Ok
                    }
                    """.formatted(condition);
            Compilation compilation = Compilation.ofSource(model, "Main");
            assertDoesNotThrow(() -> {
                compilation.measure(Adequacy.Asked.fullReport());
                compilation.answerEverything();
            }, condition);
            ACompiledModel.compiles(compilation);
            assertNotNull(Adequacy.readingsOf(compilation.db(), "demo"), condition);
            assertNotNull(compilation.db().ask(new Adequacy.Coverage("demo")).value(), condition);
        }
    }

    /**
     * The same product under a quantifier over a list, and over the values of a map: a statement
     * every element or some element meets, and a number read off the entries.
     */
    @Test
    void aProductNoOneNumberHoldsIsMeasuredUnderAQuantifierAndOverAMap() {
        for (String condition : List.of(
                "List.any(n -> (n + a) * c >= 10, ns)",
                "List.all(n -> (n + a) * c >= 10, ns)",
                "List.all(n -> (n + a) * c >= 10, ns) && a >= 5",
                "List.any(n -> (n + a) * c >= 10, ns) && List.sum(ns) >= 9",
                "List.all(n -> n * c >= 10, ns) && (a + b) * c >= 1000",
                "Map.size(Map.filterEntries((_, d) -> (d + a) * c >= 10, m)) >= 1",
                "Map.size(Map.filterEntries((_, d) -> (d + a) * c >= 10, m)) >= 1 && a >= 5",
                "List.sum(Map.values(m)) + (a + b) * c >= 1000")) {
            String model = """
                    module demo

                    data Ok
                    data No

                    behavior f : (ns: List<Int>, m: Map<String, Int>, a: Int, b: Int, c: Int)
                            -> Ok | No
                    let f (ns, m, a, b, c) = {
                        guard %s else No
                        Ok
                    }
                    """.formatted(condition);
            Compilation compilation = Compilation.ofSource(model, "Main");
            assertDoesNotThrow(() -> {
                compilation.measure(Adequacy.Asked.fullReport());
                compilation.answerEverything();
            }, condition);
            ACompiledModel.compiles(compilation);
            assertNotNull(Adequacy.readingsOf(compilation.db(), "demo"), condition);
            assertNotNull(compilation.db().ask(new Adequacy.Coverage("demo")).value(), condition);
        }
    }

    /** A product whose factor is itself a product no one number holds: the pair is not held either. */
    @Test
    void aProductBesideAProductWithNoWayIsMeasuredWithoutAnInternalError() {
        String params = "a: Decimal, b: Decimal, x: Decimal, limit: Decimal, rate: Decimal";
        assertMeasured(modelOf(params,
                "Decimal.multiply(x, Decimal.multiply(Decimal.add(a, b), rate))"));
        assertMeasured(modelOf(params,
                "Decimal.multiply(Decimal.multiply(Decimal.add(a, b), rate), x)"));
    }

    /** A product whose factor is itself a product that has a way, which keeps its target. */
    @Test
    void aProductBesideAProductWithAWayIsStillATarget() {
        NumericTerm inner = NumericTerm.ProductOf.of(LinearForm.atom(number("p")),
                LinearForm.atom(number("q")));
        NumericTerm.ProductOf outer = NumericTerm.ProductOf.of(LinearForm.atom(number("x")),
                LinearForm.atom(inner));
        assertNotNull(outer.atAValue());
        assertTrue(RealizationTarget.of(outer).isPresent());
        NumericTerm innerNoWay = NumericTerm.ProductOf.of(sumOf("a", "b"),
                LinearForm.atom(number("rate")));
        // Whichever of the two the product orders first, the pair is held by two numbers and both
        // have to be ones a row writes.
        for (String factor : List.of("0", "x", "zz")) {
            NumericTerm.ProductOf outerNoWay = NumericTerm.ProductOf.of(
                    LinearForm.atom(number(factor)), LinearForm.atom(innerNoWay));
            assertNotNull(outerNoWay, factor);
            assertEquals(Optional.empty(), RealizationTarget.of(outerNoWay), factor);
        }
    }

    /** The controls: a product that has a way, a sum beside a constant, and no product. */
    @Test
    void theControlsStillMeasure() {
        assertMeasured(modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.multiply(a, rate)"));
        assertMeasured(modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.multiply(Decimal.add(a, b), 0.1m)"));
        assertMeasured(modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.subtract(a, 1.0m)"));
    }
}
