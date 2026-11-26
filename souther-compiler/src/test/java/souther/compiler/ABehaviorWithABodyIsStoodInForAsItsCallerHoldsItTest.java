package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A behavior with a body of its own is stood in for as whatever the behavior depending on it holds it
 * as.
 *
 * <p>What a stand-in is made into is read off the constructor the caller was emitted with: the unary
 * {@code Behavior}, the base a Java-supplied behavior extends, or the interface of a behavior Souther
 * implements. Which of the three a dependency is turns on how many inputs it takes and who implements
 * it, and a stand-in means the same whichever it is.
 *
 * <p>Every model here has a row whose expectation is wrong. A row that never ran says nothing, so a
 * model whose every row is right would pass with none of them run; the wrong one is refused only if
 * it ran.
 */
class ABehaviorWithABodyIsStoodInForAsItsCallerHoldsItTest {

    private static final String STOCK = """
            module probe.stock exposing ( Shortage )

            data Shortage = { short: Int }
            """;

    /**
     * Two dependencies taking two inputs and answering a union with a member of each form: {@code Int}
     * and {@code Shortage}, which reach the union through a bridge case of the module declaring the
     * dependency, and {@code Missing}, which is a case of it. {@code price} is supplied by Java,
     * {@code convert} is implemented here and nothing stands in for the {@code lookup} its body calls.
     */
    private static final String BRIDGED = """
            module probe.bridged
            import probe.stock ( Shortage )

            data Missing = { key: Int }

            behavior lookup : (key: Int) -> Int
            behavior price : (a: Int, b: Int) -> Int | Shortage | Missing

            behavior convert : (a: Int, b: Int) -> Int | Shortage | Missing
                depends on lookup
                constructs Missing
            let convert (a, b, lookup) = if lookup(a) > b then lookup(a) else Missing { key = a }

            behavior top : (a: Int, b: Int) -> Int
                depends on convert, price
            let top (a, b, convert, price) = {
                let c = match convert(a, b) with
                    | Int as n -> n
                    | Shortage as s -> s.short + 100
                    | Missing as m -> m.key + 200
                let p = match price(a, b) with
                    | Int as n -> n
                    | Shortage as s -> s.short + 100
                    | Missing as m -> m.key + 200
                c * 1000 + p
            }
            """;

    /** Each member answered by a table, read back by the caller through the case it reached. */
    @Test
    void aMemberReachingTheUnionThroughABridgeIsAnsweredByATable() {
        ACompiledModel.refusedWith(List.of("E1905"), together(List.of(STOCK, BRIDGED + """

                fake convert
                    | (1, 2) -> 7
                    | (2, 1) -> Shortage { short = 3 }
                    | (3, 3) -> Missing { key = 4 }

                fake price
                    | (1, 2) -> Missing { key = 5 }
                    | (2, 1) -> 6
                    | (3, 3) -> Shortage { short = 8 }

                example top
                    | "an Int and a Missing" : (1, 2) -> 7205
                    | "a Shortage and an Int" : (2, 1) -> 103006
                    | "a Missing and a Shortage" : (3, 3) -> 204108
                    | "and not this" : (1, 2) -> 1
                """)));
    }

    /** The same members answered by the row. */
    @Test
    void aMemberReachingTheUnionThroughABridgeIsAnsweredByAWith() {
        ACompiledModel.refusedWith(List.of("E1905"), together(List.of(STOCK, BRIDGED + """

                example top
                    | "an Int and a Missing" : (1, 2)
                        with convert = 7, price = Missing { key = 5 } -> 7205
                    | "a Shortage and an Int" : (2, 1)
                        with convert = Shortage { short = 3 }, price = 6 -> 103006
                    | "a Missing and a Shortage" : (3, 3)
                        with convert = Missing { key = 4 }, price = Shortage { short = 8 } -> 204108
                    | "and not this" : (1, 2)
                        with convert = 7, price = Missing { key = 5 } -> 1
                """)));
    }

    /** A behavior another module implements, taking two inputs, with a requirement of its own. */
    private static final String RATES = """
            module probe.rates exposing ( convert )

            behavior lookup : (key: Int) -> Int

            behavior convert : (a: Int, b: Int) -> Int
                depends on lookup
            let convert (a, b, lookup) = lookup(a) + b
            """;

    private static final String CONVERTING = """
            module probe.converting
            import probe.rates ( convert )

            behavior top : (a: Int, b: Int) -> Int
                depends on convert
            let top (a, b, convert) = convert(a, b) + convert(b, a)

            fake convert
                | (1, 2) -> 10
                | (2, 1) -> 20

            example top
                | "both orders" : (1, 2) -> 30
            """;

    private static final String CONVERTING_WRONGLY = CONVERTING.replace("-> 30", "-> 31");

    /** Compiled with the module that stands in for it. */
    @Test
    void aBehaviorAnotherModuleImplementsIsStoodInForCompiledTogether() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(RATES, CONVERTING)));
        assertEquals("E1905", assertThrows(CompileException.class,
                        () -> Compiler.compileModules(List.of(RATES, CONVERTING_WRONGLY)))
                .diagnostic().code(), "the row is run, so a wrong answer is refused");
    }

    /** Read off the path, as its compiled classes. */
    @Test
    void aBehaviorAnotherModuleImplementsIsStoodInForReadOffThePath() {
        Map<String, ClassFileImage> rates = Compiler.compile(RATES);

        assertDoesNotThrow(() -> Compiler.compileModules(List.of(CONVERTING), ModulePath.of(rates)));
        assertEquals("E1905", assertThrows(CompileException.class,
                        () -> Compiler.compileModules(List.of(CONVERTING_WRONGLY),
                                ModulePath.of(rates)))
                .diagnostic().code(), "the row is run, so a wrong answer is refused");
    }

    /** A table with no row for a call the body makes stops the row there (E1909). */
    @Test
    void aCallTheTableHasNoRowForStopsTheRow() {
        ACompiledModel.refusedWith(List.of("E1909"), together(List.of(RATES, CONVERTING.replace(
                "| (2, 1) -> 20", "| (3, 3) -> 20"))));
    }

    /** A behavior implemented here, taking two inputs, that declares what it answers. */
    private static final String KEPT = """
            module probe.kept

            behavior lookup : (key: Int) -> Int

            behavior convert : (a: Int, b: Int) -> Int
                depends on lookup
                ensures bounded = value < a + 100
            let convert (a, b, lookup) = lookup(a) + b

            behavior top : (a: Int, b: Int) -> Int
                depends on convert
            let top (a, b, convert) = convert(a, b)
            """;

    /** A table row stating an answer the declaration rules out is refused where it is written. */
    @Test
    void aTableRowTheDeclarationRulesOutIsRefused() {
        ACompiledModel.refusedWith(List.of("E1929"), together(List.of(KEPT + """

                fake convert
                    | (1, 2) -> 500

                example top
                    | "past the bound" : (1, 2) -> 500
                """)));
    }

    /** The modules of {@code sources}, compiled together. */
    private static Compilation together(List<String> sources) {
        return Compilation.ofSources(sources, ModulePath.EMPTY);
    }
}
