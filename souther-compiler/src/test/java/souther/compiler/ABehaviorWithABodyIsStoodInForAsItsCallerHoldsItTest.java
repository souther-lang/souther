package souther.compiler;

import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Output;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Modifier;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A behavior with a body of its own is stood in for as whatever the behavior depending on it holds it
 * as.
 *
 * <p>What a stand-in is made into is read off the constructor the caller was emitted with: the unary
 * {@code Behavior}, the base a Java-supplied behavior extends, or the interface of a behavior Souther
 * implements. Which of the three a dependency is turns on how many inputs it takes and who implements
 * it, and a stand-in means the same whichever it is.
 *
 * <p>Each model exposes only the behavior its rows are about, so every dependency Souther implements
 * is a class its module does not expose.
 *
 * <p>A row is held to having been compared and held, and not to having said nothing: a row that
 * never ran says nothing too.
 */
class ABehaviorWithABodyIsStoodInForAsItsCallerHoldsItTest {

    /**
     * A behavior one constructor takes dependencies of every kind for: implemented in Souther (its
     * own {@code depends on} makes it one that may be depended on, spec §depends-on) taking none, two
     * and three inputs, and supplied by Java taking two.
     *
     * <p>Each kind is held as a different class, and one constructor takes them side by side, so a
     * stand-in made into the wrong one, or handed to the wrong place, is a row that does not run.
     * Nothing stands in for {@code lookup}: a row reaching a stood-in behavior's own body would have
     * nothing to call it with.
     */
    private static final String LAYERED = """
            module probe.layered exposing ( top )

            behavior lookup : (key: Int) -> Int
            behavior rate : (a: Int, b: Int) -> Int

            behavior stamp : () -> Int
                depends on lookup
            let stamp (lookup) = lookup(0)

            behavior convert : (a: Int, b: Int) -> Int
                depends on lookup
            let convert (a, b, lookup) = lookup(a) + b

            behavior blend : (a: Int, b: Int, c: Int) -> Int
                depends on lookup
            let blend (a, b, c, lookup) = lookup(a) + b + c

            behavior top : (a: Int, b: Int) -> Int
                depends on stamp, convert, blend, rate
            let top (a, b, stamp, convert, blend, rate) =
                stamp() + convert(a, b) + blend(a, b, 1) + rate(a, b)
            """;

    /**
     * What the model's dependencies are emitted as: the interfaces of the three Souther implements,
     * none of them public.
     */
    @Test
    void theDependenciesImplementedInSoutherAreClassesTheModuleDoesNotExpose() throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compile(LAYERED + """

                fake stamp
                    | _ -> 100
                """);
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        for (String dependency : List.of("Stamp", "Convert", "Blend")) {
            Class<?> held = loader.loadClass("probe.layered." + dependency);
            assertFalse(Modifier.isPublic(held.getModifiers()), held + " is not exposed");
            assertEquals(true, held.isInterface(), held + " is the interface of what Souther implements");
        }
    }

    /**
     * Each dependency stood in for by its table, whatever count of inputs it takes. The two rows tell
     * {@code (1, 2)} from {@code (2, 1)}, so each stand-in is handed every argument in the order the
     * call wrote it.
     */
    @Test
    void aDependencyImplementedInSoutherIsStoodInForByItsTableWhateverItTakes() {
        held(rows(List.of(), together(LAYERED + """

                fake stamp
                    | _ -> 100

                fake convert
                    | (1, 2) -> 10
                    | (2, 1) -> 20

                fake blend
                    | (1, 2, 1) -> 1000
                    | (2, 1, 1) -> 2000

                fake rate
                    | (1, 2) -> 5
                    | (2, 1) -> 7

                example top
                    | "one then two" : (1, 2) -> 1115
                    | "two then one" : (2, 1) -> 2127
                """), "probe.layered"), "one then two", "two then one");
    }

    /** The same dependencies stood in for by a {@code with} on the row, over their tables. */
    @Test
    void aDependencyImplementedInSoutherIsStoodInForByAWithWhateverItTakes() {
        held(rows(List.of(), together(LAYERED + """

                fake convert
                    | _ -> 10

                example top
                    | "each as the row says" : (1, 2)
                        with stamp = 1, convert = 20, blend = 300, rate = 4000 -> 4321
                """), "probe.layered"), "each as the row says");
    }

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
            module probe.bridged exposing ( top )
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
        held(rows(List.of(), Compilation.ofSources(List.of(STOCK, BRIDGED + """

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
                """), ModulePath.EMPTY), "probe.bridged"),
                "an Int and a Missing", "a Shortage and an Int", "a Missing and a Shortage");
    }

    /** The same members answered by the row. */
    @Test
    void aMemberReachingTheUnionThroughABridgeIsAnsweredByAWith() {
        held(rows(List.of(), Compilation.ofSources(List.of(STOCK, BRIDGED + """

                example top
                    | "an Int and a Missing" : (1, 2)
                        with convert = 7, price = Missing { key = 5 } -> 7205
                    | "a Shortage and an Int" : (2, 1)
                        with convert = Shortage { short = 3 }, price = 6 -> 103006
                    | "a Missing and a Shortage" : (3, 3)
                        with convert = Missing { key = 4 }, price = Shortage { short = 8 } -> 204108
                """), ModulePath.EMPTY), "probe.bridged"),
                "an Int and a Missing", "a Shortage and an Int", "a Missing and a Shortage");
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

    /** Compiled with the module that stands in for it. */
    @Test
    void aBehaviorAnotherModuleImplementsIsStoodInForCompiledTogether() {
        held(rows(List.of(), Compilation.ofSources(List.of(RATES, CONVERTING), ModulePath.EMPTY),
                "probe.converting"), "both orders");
    }

    /** Read off the path, as its compiled classes. */
    @Test
    void aBehaviorAnotherModuleImplementsIsStoodInForReadOffThePath() {
        held(rows(List.of(), Compilation.ofSources(List.of(CONVERTING),
                ModulePath.of(Compiler.compile(RATES))), "probe.converting"), "both orders");
    }

    /**
     * A behavior another module implements that answers a union, one of whose members a third
     * module declares. Three modules each own one part of the answer: {@code probe.stock} the type
     * {@code Shortage}, {@code probe.supply} the union and the bridge case {@code Shortage} and
     * {@code Int} reach it through, and {@code probe.ordering} the rows. Read off the path, so the
     * union and its bridge cases are classes another build emitted.
     */
    private static final String SUPPLY = """
            module probe.supply exposing ( Missing, supply )
            import probe.stock ( Shortage )

            data Missing = { key: Int }

            behavior lookup : (key: Int) -> Int

            behavior supply : (a: Int, b: Int) -> Int | Shortage | Missing
                depends on lookup
                constructs Missing
            let supply (a, b, lookup) = if lookup(a) > b then lookup(a) else Missing { key = a }
            """;

    private static final String ORDERING = """
            module probe.ordering exposing ( top )
            import probe.stock ( Shortage )
            import probe.supply ( Missing, supply )

            behavior top : (a: Int, b: Int) -> Int
                depends on supply
            let top (a, b, supply) = match supply(a, b) with
                | Int as n -> n
                | Shortage as s -> s.short + 100
                | Missing as m -> m.key + 200

            fake supply
                | (1, 2) -> 7
                | (2, 1) -> Shortage { short = 3 }
                | (3, 3) -> Missing { key = 4 }

            example top
                | "an Int" : (1, 2) -> 7
                | "a Shortage" : (2, 1) -> 103
                | "a Missing" : (3, 3) -> 204
            """;

    @Test
    void aUnionAnotherModuleAnswersWithAThirdModulesTypeIsStoodInForReadOffThePath() {
        held(rows(List.of(), Compilation.ofSources(List.of(ORDERING),
                ModulePath.of(Compiler.compileModules(List.of(STOCK, SUPPLY)))),
                "probe.ordering"), "an Int", "a Shortage", "a Missing");
    }

    /** A table with no row for a call the body makes stops the row there (E1909). */
    @Test
    void aCallTheTableHasNoRowForStopsTheRow() {
        RowOutcome row = rows(List.of("E1909"), Compilation.ofSources(List.of(RATES,
                CONVERTING.replace("| (2, 1) -> 20", "| (3, 3) -> 20")), ModulePath.EMPTY),
                "probe.converting").get("both orders");

        assertEquals(Disposition.FAILED, row.disposition(), row.toString());
    }

    /** A behavior implemented here, taking two inputs, that declares what it answers. */
    private static final String KEPT = """
            module probe.kept exposing ( top )

            behavior lookup : (key: Int) -> Int

            behavior convert : (a: Int, b: Int) -> Int
                depends on lookup
                ensures bounded = value < a + 100
            let convert (a, b, lookup) = lookup(a) + b

            behavior top : (a: Int, b: Int) -> Int
                depends on convert
            let top (a, b, convert) = convert(a, b)
            """;

    /**
     * A table row stating an answer the declaration rules out is refused where it is written, and a
     * row reaching the table does not run against it.
     */
    @Test
    void aTableRowTheDeclarationRulesOutIsRefused() {
        RowOutcome row = rows(List.of("E1929"), together(KEPT + """

                fake convert
                    | (1, 2) -> 500

                example top
                    | "past the bound" : (1, 2) -> 500
                """), "probe.kept").get("past the bound");

        assertEquals(List.of(Disposition.FAILED, FailurePhase.FAKE_RESOLUTION),
                List.of(row.disposition(), row.failurePhase()), row.toString());
    }

    private static Compilation together(String source) {
        return Compilation.ofSources(List.of(source), ModulePath.EMPTY);
    }

    /**
     * Every row {@code module}'s examples write, by its name, once the compilation is held to be
     * refused with {@code codes} and nothing else.
     */
    private static Map<String, RowOutcome> rows(List<String> codes, Compilation compilation,
                                                String module) {
        ACompiledModel.refusedWith(codes, compilation);
        Db db = compilation.db();
        Map<String, RowOutcome> rows = new LinkedHashMap<>();
        for (RowOutcome row : db.ask(new Output.Examples(module,
                compilation.sourceIdOf(module))).value().rows()) {
            rows.put(row.identity() instanceof RowIdentity.Named(String name) ? name
                    : String.valueOf(row.identity()), row);
        }
        return rows;
    }

    /** That the rows are {@code names}, and every one of them was compared and held. */
    private static void held(Map<String, RowOutcome> rows, String... names) {
        assertEquals(List.of(names), List.copyOf(rows.keySet()), "the rows the model writes");
        rows.forEach((name, row) -> assertEquals(
                List.of(Stage.COMPARED, Disposition.HELD, FailurePhase.NONE),
                List.of(row.stage(), row.disposition(), row.failurePhase()), name + ": " + row));
    }
}
