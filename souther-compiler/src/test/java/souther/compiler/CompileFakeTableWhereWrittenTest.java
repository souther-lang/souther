package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.Located;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code fake}'s table is built because it is written, not because something reads it.
 *
 * <p>A table is read to stand in for a behavior while a row of something that depends on it runs, and
 * read again against the rows recorded for the behavior itself. A module can write one that neither
 * of those reaches — nothing depends on the faked behavior, and no row records what it owes — and
 * what is wrong with such a table was said nowhere: the reading built it into a list nobody read, and
 * nothing else built it at all.
 */
class CompileFakeTableWhereWrittenTest {

    /** A behavior nothing depends on, with rows of its own: the reading is the only other place its
     * table is built, and it does not report. */
    private static final String UNREAD = """
            module example.written

            data N = Int
            data Found = { n: N }
            data Missing = { why: String }

            behavior find : (n: N) -> Found | Missing
                constructs Found

            let find (n) = Found { n = n }

            example find
                | "one" : (N(1)) -> Found { n = N(1) }
            """;

    /** An injected dependency and a behavior whose rows run against a stand-in for it. */
    private static final String INJECTED = """
            module example.used

            data N = Int
            data Found = { n: N }
            data Missing = { why: String }
            data Ok = { n: N }

            behavior find : (n: N) -> Found | Missing

            behavior use : (n: N) -> Ok | Missing
                depends on find
                constructs Ok, Missing

            let use (n, find) = match find(n) with
                | Found   -> Ok { n = n }
                | Missing -> Missing { why = "none" }
            """;

    @Test
    void aTableNoRowReadsIsStillBuilt() {
        // `N` is a newtype over Int, so `N("x")` is a row that will not build. Nothing depends on
        // `find`, so no row ever stands in with this table; it says what it says all the same.
        Diagnostic one = only(UNREAD + """

                fake find
                    | (N("x")) -> Found { n = N(1) }
                """);

        assertEquals("E1908", one.code());
        assertEquals("example.the-fake-could-not-be-built", one.messageKey());
        assertEquals("find", one.values().get("dependency"),
                "the behavior the table stands in for");
        assertEquals(15, one.pos().line(), "at the fake, which is where the table is written");
    }

    @Test
    void aTableNothingAtAllReadsIsStillBuilt() {
        // No rows recorded for `find` either, so not even the reading builds this one.
        Diagnostic one = only("""
                module example.alone

                data N = Int
                data Found = { n: N }
                data Missing = { why: String }

                behavior find : (n: N) -> Found | Missing
                    constructs Found

                let find (n) = Found { n = n }

                fake find
                    | (N("x")) -> Found { n = N(1) }
                """);

        assertEquals("E1908", one.code());
        assertEquals("example.the-fake-could-not-be-built", one.messageKey());
    }

    @Test
    void aRowOfTheWrongArityIsSaidWithoutARowReadingTheTable() {
        Diagnostic one = only(UNREAD + """

                fake find
                    | (N(1), N(2)) -> Found { n = N(1) }
                """);

        assertEquals("E1908", one.code());
        assertEquals("example.the-fake-could-not-be-built", one.messageKey());
        assertEquals(16, one.pos().line(), "at the row whose input count is wrong");
    }

    /**
     * A second table written for one dependency is not built here either.
     *
     * <p>The first is the one that answers — it is what stands in ({@code resolveFake}) and what the
     * rows are read against — so a second states nothing anywhere. Building it here would hold a
     * table to something no reader of it would ever ask.
     */
    @Test
    void aSecondTableForOneDependencyIsNotBuilt() {
        assertDoesNotThrow(() -> Compiler.compile(UNREAD + """

                fake find
                    | (N(1)) -> Found { n = N(1) }

                fake find
                    | (N("x")) -> Found { n = N(1) }
                """));
    }

    /** And a table that builds is said nowhere: the check is not one every fake fails. */
    @Test
    void aTableThatBuildsIsSaidNowhere() {
        assertDoesNotThrow(() -> Compiler.compile(UNREAD + """

                fake find
                    | (N(1)) -> Found { n = N(1) }
                """));
    }

    /**
     * One table, one report, however many rows read it.
     *
     * <p>A row that applies a fake it could not build does not run, and what is wrong with the table
     * is not the row's to say: each row reaching it would otherwise repeat the one thing wrong with
     * the one table they all read.
     */
    @Test
    void oneTableIsSaidOnceHoweverManyRowsReadIt() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(INJECTED + """

                example use
                    | "one" : (N(1)) -> Ok { n = N(1) }
                    | "two" : (N(2)) -> Ok { n = N(2) }

                fake find
                    | (N("x")) -> Found { n = N(1) }
                """));

        assertEquals(List.of("E1908"), codesOf(e), e.getMessage());
        assertEquals("example.the-fake-could-not-be-built", e.diagnostics().get(0).messageKey());
    }

    /** A fake written in an attached file is built for that file, and said in it. */
    @Test
    void aFakeInAnAttachedFileIsSaidInThatFile() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(INJECTED + """

                        example use
                            | "one" : (N(1)) -> Ok { n = N(1) }
                        """, """
                        examples for example.used

                        fake find
                            | (N("x")) -> Found { n = N(1) }
                        """)));

        assertEquals(List.of("E1908"), codesOf(e), e.getMessage());
        assertEquals("1", e.sourceIdOf(0), "the file that wrote the fake is the file it is said in");
    }

    /**
     * A table whose fixture loops spends the budget the policy allows, and is reported for that.
     *
     * <p>Said as a fact rather than by writing something slow and waiting: the helper the table
     * applies goes round forever, the budget is small, and what comes back is the same on every host.
     * That is what the counting is for, and it is why this test needs no deadline of its own.
     */
    @Test
    void aTableWhoseFixtureLoopsIsReportedForSpendingItsSteps() {
        List<Located> warnings = new ArrayList<>();
        assertDoesNotThrow(() -> Compiler.compiled("""
                module example.slow

                data N = Int
                data Found = { n: N }
                data Missing = { why: String }

                partial let spin (n: Int): Int = spin(n)

                behavior find : (n: N) -> Found | Missing
                    constructs Found

                let find (n) = Found { n = n }

                fake find
                    | (N(spin(1))) -> Found { n = N(1) }
                """, "Main", warnings, souther.compiler.query.Adequacy.Asked.NOTHING,
                EvaluationPolicy.of(10_000L)));

        List<Located> said = only("E1921", warnings);
        assertEquals(1, said.size(), warnings.toString());
        Diagnostic one = said.get(0).diagnostic();
        assertTrue(rendered(one).contains("Building the `fake find` table spent its budget of"
                        + " 10000 steps"),
                rendered(one));
    }

    /**
     * A table that did not finish being built says so, and says nothing about being wrong: waiting
     * tells the two apart in neither direction. Nothing reads this one — no row depends on `find` and
     * none is recorded for it — so the comparison the reading would report on (E1920) never arises,
     * and this is the only thing said about the table.
     */
    @Test
    void aTableThatDidNotFinishBuildingSaysSoAtTheFake() {
        List<Located> warnings = new ArrayList<>();
        assertDoesNotThrow(() -> Compiler.compiled("""
                module example.slow

                data N = Int
                data Found = { n: N }
                data Missing = { why: String }

                partial let spin (n: Int): Int = spin(n)

                behavior find : (n: N) -> Found | Missing
                    constructs Found

                let find (n) = Found { n = n }

                fake find
                    | (N(spin(1))) -> Found { n = N(1) }
                """, "Main", warnings, souther.compiler.query.Adequacy.Asked.NOTHING,
                null, DoesNotComeBack.overrunningOn(DoesNotComeBack.everyTableOf("find"))));

        List<Located> said = only("E1921", warnings);
        assertEquals(1, said.size(), warnings.toString());
        assertEquals(List.of(), only("E1920", warnings),
                "nothing records what `find` owes, so no comparison was missed");
        Diagnostic one = said.get(0).diagnostic();
        assertEquals(14, one.pos().line(), "at the fake");
        assertEquals(6, one.pos().column(), "on the behavior it names");
        // The number is read off the wait this compile was given rather than written in, so the
        // line still holds if that wait changes. Ungrouped, which is how it is set.
        assertTrue(rendered(one).contains("Building the `fake find` table did not answer within "
                        + DoesNotComeBack.BUDGET.toMillis() + "ms"),
                rendered(one));
        assertTrue(rendered(one).contains("not code this compile generated"),
                "the hint says whose fault it is not: " + rendered(one));
    }

    /** The one diagnostic of a compile that has one. */
    private static Diagnostic only(String model) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(model));
        assertEquals(1, e.diagnostics().size(), "one table, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    private static List<String> codesOf(CompileException e) {
        List<String> codes = new ArrayList<>();
        for (Diagnostic d : e.diagnostics()) {
            codes.add(d.code());
        }
        return codes;
    }

    private static List<Located> only(String code, List<Located> warnings) {
        List<Located> found = new ArrayList<>();
        for (Located w : warnings) {
            if (code.equals(w.diagnostic().code())) {
                found.add(w);
            }
        }
        return found;
    }

    private static String rendered(Diagnostic d) {
        return new HumanRenderer(false).render(d, null, Locale.ENGLISH);
    }
}
