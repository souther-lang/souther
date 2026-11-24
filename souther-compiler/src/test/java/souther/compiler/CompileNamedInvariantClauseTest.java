package souther.compiler;

import souther.compiler.diag.Primary;

import souther.compiler.diag.msg.InvariantMessage;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An invariant clause declared with a name, and the attempted construction that departs by the clause
 * that did not hold: {@code guard T(v) as x else | nonEmpty -> NoItems | unique -> DuplicateItem}.
 *
 * <p>What the arms answer is which rule failed, not what the failure is worth — the name a business
 * failure gets is still the one written in the arm (ADR-0070). A clause declared without a name is
 * enforced as before: nothing tells it apart from the type's other unnamed clauses, and {@code | _ ->}
 * is what answers all of them.
 */
class CompileNamedInvariantClauseTest {

    /** {@code clauses} are the invariant lines of {@code Items}, {@code departure} the whole
     * {@code else} of the attempt — written out rather than patched into a fixed module, so a change
     * that stops matching cannot pass as the unchanged module. */
    private static String module(String clauses, String departure) {
        return """
                module demo

                data NoItems
                data DuplicateItem
                data Accepted = { items: Items }

                data Items = List<Int>
                %s

                behavior build : (xs: List<Int>) -> Accepted | NoItems | DuplicateItem
                    constructs Accepted, Items

                let build (xs) = {
                    guard Items(xs) as items else%s

                    Accepted { items = items }
                }
                """.formatted(clauses, departure);
    }

    private static final String TWO_NAMED = """
                invariant nonEmpty = List.length(value) >= 1
                invariant unique = List.allDistinctBy(x -> x, value)""";

    private static Object build(BytesClassLoader loader, List<Long> xs) throws Exception {
        Object impl = Emitted.behavior(loader, "demo", "build").getConstructor().newInstance();
        return Codecs.apply(impl, xs);
    }

    private static String departs(String clauses, String departure, List<Long> xs) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module(clauses, departure)),
                CompileNamedInvariantClauseTest.class.getClassLoader());
        return build(loader, xs).getClass().getName();
    }

    /**
     * The arm taken is the arm of the first clause, in the order the clauses are declared, that the
     * value breaks, and the order the arms are written in changes nothing. A value that breaks both is
     * reported as the first, so reordering the declaration is a change to what a caller sees. The
     * value breaking none is accepted. Every order of the declarations and of the arms is tried.
     */
    @Test
    void theArmOfTheFirstClauseInDeclarationOrderThatFailsIsTaken() throws Exception {
        String nonEmpty = "invariant nonEmpty = List.length(value) >= 3";
        String unique = "invariant unique = List.allDistinctBy(x -> x, value)";
        String nonEmptyArm = "| nonEmpty -> NoItems";
        String uniqueArm = "| unique   -> DuplicateItem";
        // [1, 1] is both shorter than three and repeating
        List<List<Long>> inputs = List.of(List.of(), List.of(1L), List.of(1L, 1L), List.of(1L, 2L),
                List.of(1L, 1L, 1L), List.of(1L, 2L, 3L));
        for (boolean nonEmptyDeclaredFirst : List.of(true, false)) {
            String clauses = nonEmptyDeclaredFirst
                    ? "    " + nonEmpty + "\n    " + unique
                    : "    " + unique + "\n    " + nonEmpty;
            for (boolean nonEmptyArmFirst : List.of(true, false)) {
                String arms = "\n        " + (nonEmptyArmFirst
                        ? nonEmptyArm + "\n        " + uniqueArm
                        : uniqueArm + "\n        " + nonEmptyArm);
                BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module(clauses, arms)),
                        CompileNamedInvariantClauseTest.class.getClassLoader());
                for (List<Long> xs : inputs) {
                    boolean tooShort = xs.size() < 3;
                    boolean repeats = new HashSet<>(xs).size() < xs.size();
                    String expected = tooShort && repeats
                            ? (nonEmptyDeclaredFirst ? "demo.NoItems" : "demo.DuplicateItem")
                            : tooShort ? "demo.NoItems"
                            : repeats ? "demo.DuplicateItem"
                            : "demo.Accepted";
                    assertEquals(expected, build(loader, xs).getClass().getName(),
                            xs + ", " + (nonEmptyDeclaredFirst ? "nonEmpty" : "unique")
                                    + " declared first, " + (nonEmptyArmFirst ? "nonEmpty" : "unique")
                                    + " arm first");
                }
            }
        }
    }

    /** The plain {@code else} form keeps working on a type with named clauses: a site that does not
     * care which rule broke says so by giving one value. */
    @Test
    void oneElseValueStillAnswersAnyFailure() throws Exception {
        String src = """
                module demo

                data NoItems
                data Accepted = { items: Items }

                data Items = List<Int>
                    invariant nonEmpty = List.length(value) >= 1
                    invariant unique = List.allDistinctBy(x -> x, value)

                behavior build : (xs: List<Int>) -> Accepted | NoItems
                    constructs Accepted, Items

                let build (xs) = {
                    guard Items(xs) as items else NoItems

                    Accepted { items = items }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src),
                getClass().getClassLoader());
        assertEquals("demo.NoItems", build(loader, List.of()).getClass().getName());
        assertEquals("demo.NoItems", build(loader, List.of(1L, 1L)).getClass().getName(),
                "one value answers any failure, whichever clause it was");
    }

    /** A clause carrying no name is answered by {@code | _ ->}, and only there. */
    @Test
    void anUnnamedClauseIsAnsweredByTheWildcard() throws Exception {
        String oneUnnamed = """
                    invariant nonEmpty = List.length(value) >= 1
                    invariant List.allDistinctBy(x -> x, value)""";
        String withWildcard = """

                        | nonEmpty -> NoItems
                        | _        -> DuplicateItem""";
        assertEquals("demo.NoItems", departs(oneUnnamed, withWildcard, List.of()));
        assertEquals("demo.DuplicateItem", departs(oneUnnamed, withWildcard, List.of(1L, 1L)));
    }

    /** The {@code if} form is the base one (ADR-0020), so it takes the same arms. */
    @Test
    void theIfFormTakesTheSameArms() throws Exception {
        String src = """
                module demo

                data NoItems
                data DuplicateItem
                data Accepted = { items: Items }

                data Items = List<Int>
                    invariant nonEmpty = List.length(value) >= 1
                    invariant unique = List.allDistinctBy(x -> x, value)

                behavior build : (xs: List<Int>) -> Accepted | NoItems | DuplicateItem
                    constructs Accepted, Items

                let build (xs) =
                    if Items(xs) as items
                    then Accepted { items = items }
                    else
                        | nonEmpty -> NoItems
                        | unique   -> DuplicateItem
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src),
                getClass().getClassLoader());
        assertEquals("demo.Accepted", build(loader, List.of(1L, 2L)).getClass().getName());
        assertEquals("demo.NoItems", build(loader, List.of()).getClass().getName());
        assertEquals("demo.DuplicateItem", build(loader, List.of(1L, 1L)).getClass().getName());
    }

    /** The arms are emitted in value position as well as in tail position: bound to a {@code let}, the
     * departure's value continues the body rather than returning from it. */
    @Test
    void theArmsAreTakenInValuePositionToo() throws Exception {
        String src = """
                module demo

                data Items = List<Int>
                    invariant nonEmpty = List.length(value) >= 1
                    invariant unique = List.allDistinctBy(x -> x, value)

                data Verdict = { code: Int }

                behavior judge : (xs: List<Int>) -> Verdict
                    constructs Verdict, Items

                let judge (xs) = {
                    let code =
                        if Items(xs) as items
                        then List.length(items.value)
                        else
                            | nonEmpty -> 0
                            | unique   -> -1

                    Verdict { code = code }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src),
                getClass().getClassLoader());
        Object impl = Emitted.behavior(loader, "demo", "judge").getConstructor().newInstance();
        assertEquals(Map.of("code", 2L),
                Codecs.encode(loader, "demo.Verdict", Codecs.apply(impl, List.of(1L, 2L))));
        assertEquals(Map.of("code", 0L),
                Codecs.encode(loader, "demo.Verdict", Codecs.apply(impl, List.of())));
        assertEquals(Map.of("code", -1L),
                Codecs.encode(loader, "demo.Verdict", Codecs.apply(impl, List.of(1L, 1L))));
    }

    /** A name is what an arm and a boundary issue call one rule, so two rules cannot share one —
     * whether both are written on the type or one arrives by a spread. */
    @Test
    void twoClausesCannotShareAName() {
        for (String source : List.of("""
                module demo
                data Items = List<Int>
                    invariant same = List.length(value) >= 1
                    invariant same = List.allDistinctBy(x -> x, value)
                """, """
                module demo
                data Common = { total: Int }
                    invariant sound = total >= 1
                data Order = { ...Common, lines: Int }
                    invariant sound = lines >= 1
                """)) {
            CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(source));
            assertInstanceOf(InvariantMessage.TwoClausesShareOneName.class, e.diagnostics().get(0).said());
        }
    }

    /**
     * `_` is what an attempt writes for the clauses that carry no name, so a clause named `_` could not
     * be answered by name — the arm reading it would be that wildcard, and the clause would stay
     * unanswered. Refused where the clause is declared, not where an attempt fails to answer it.
     */
    @Test
    void underscoreCannotNameAClause() {
        String source = """
                module demo
                data Positive = Int
                    invariant _ = value > 0
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(source));
        assertInstanceOf(InvariantMessage.UnderscoreCannotNameAClause.class, e.diagnostics().get(0).said());
        assertEquals(3, WhereItSits.in(source, ((Primary.InSource) e.diagnostics().get(0).primary()).place().region()).start().line(), "reported at the clause, not at a use");
    }

    /** A clause arriving by spread carries its name: the invariants a {@code ...} takes in are checked
     * where the spreading type is built (spec §field-spread), and an arm names them as their own
     * declaration did. */
    @Test
    void aSpreadCarriesItsClauseNames() throws Exception {
        String src = """
                module demo

                data Common = { total: Int }
                    invariant positiveTotal = total >= 1

                data Order = { ...Common, lines: Int }
                    invariant hasLines = lines >= 1

                data NoTotal
                data NoLines
                data Request = { total: Int, lines: Int }
                data Fine = { order: Order }

                behavior make : (req: Request) -> Fine | NoTotal | NoLines
                    constructs Fine, Order

                let make (req) = {
                    guard Order { total = req.total, lines = req.lines } as order else
                        | positiveTotal -> NoTotal
                        | hasLines      -> NoLines

                    Fine { order = order }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src),
                getClass().getClassLoader());
        Object impl = Emitted.behavior(loader, "demo", "make").getConstructor().newInstance();
        assertEquals("demo.Fine", make(loader, impl, 5L, 1L), "neither clause is broken");
        assertEquals("demo.NoTotal", make(loader, impl, 0L, 1L),
                "the clause the spread brought in decides, under the name its declaration gave it");
        assertEquals("demo.NoLines", make(loader, impl, 5L, 0L));
    }

    private static String make(BytesClassLoader loader, Object impl, long total, long lines)
            throws Exception {
        Object req = Codecs.decoded(loader, "demo.Request", Map.of("total", total, "lines", lines));
        return Codecs.apply(impl, req).getClass().getName();
    }

    /**
     * An importing module names the clauses of an imported type. A declaration travels with the class
     * that carries it (ADR-0063), clause names included, which is what makes this the form that works
     * across a module boundary where restating the rule cannot: the helper an invariant names is not
     * exposable, and the type is.
     */
    @Test
    void anImportedTypesClausesAreNamedByTheImporter() {
        Compiler.compileModules(List.of("""
                module up exposing ( Items )
                data Items = List<Int>
                    invariant nonEmpty = List.length(value) >= 1
                    invariant unique = List.allDistinctBy(x -> x, value)
                """, """
                module down
                import up ( Items )

                data NoItems
                data DuplicateItem
                data Accepted = { items: Items }

                behavior build : (xs: List<Int>) -> Accepted | NoItems | DuplicateItem
                    constructs Accepted, Items

                let build (xs) = {
                    guard Items(xs) as items else
                        | nonEmpty -> NoItems
                        | unique   -> DuplicateItem

                    Accepted { items = items }
                }
                """));
    }

    @Test
    void anArmNamingNoClauseOfAnImportedTypeIsReported() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compileModules(List.of("""
                module up exposing ( Items )
                data Items = List<Int>
                    invariant nonEmpty = List.length(value) >= 1
                """, """
                module down
                import up ( Items )

                data NoItems
                data Accepted = { items: Items }

                behavior build : (xs: List<Int>) -> Accepted | NoItems
                    constructs Accepted, Items

                let build (xs) = {
                    guard Items(xs) as items else
                        | notEmpty -> NoItems

                    Accepted { items = items }
                }
                """)));
        assertEquals("E2014", e.code());
    }

    // --- what the arms must answer ---

    private static CompileException armError(String clauses, String departure) {
        return assertThrows(CompileException.class,
                () -> Compiler.compile(module(clauses, departure)));
    }

    @Test
    void anArmNamingNoClauseOfTheTypeIsReported() {
        assertEquals("E2014", armError(TWO_NAMED, """

                        | nonEmpty -> NoItems
                        | uniq     -> DuplicateItem""").code());
    }

    @Test
    void aClauseWithNoArmIsReported() {
        assertEquals("E2015", armError(TWO_NAMED, """

                        | nonEmpty -> NoItems""").code());
    }

    @Test
    void anUnnamedClauseWithNoWildcardIsReported() {
        String oneUnnamed = """
                    invariant nonEmpty = List.length(value) >= 1
                    invariant List.allDistinctBy(x -> x, value)""";
        assertEquals("E2016", armError(oneUnnamed, """

                        | nonEmpty -> NoItems""").code());
    }

    @Test
    void aWildcardWhereEveryClauseIsNamedIsReported() {
        assertEquals("E2017", armError(TWO_NAMED, """

                        | nonEmpty -> NoItems
                        | unique   -> DuplicateItem
                        | _        -> NoItems""").code());
    }

    @Test
    void theSameClauseAnsweredTwiceIsReported() {
        assertEquals("E2019", armError(TWO_NAMED, """

                        | nonEmpty -> NoItems
                        | nonEmpty -> DuplicateItem
                        | unique   -> DuplicateItem""").code());
    }

    /** Arms answer the clauses of a construction being attempted, so a plain condition has none. */
    @Test
    void armsWithoutAnAttemptAreReported() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data NoItems
                data Accepted

                behavior build : (xs: List<Int>) -> Accepted | NoItems
                    constructs Accepted

                let build (xs) = {
                    guard List.length(xs) >= 1 else
                        | nonEmpty -> NoItems

                    Accepted
                }
                """));
        assertEquals("E2018", e.code());
    }
}
