package souther.compiler.query;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.Located;
import souther.compiler.diag.Primary;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A report about a declaration is sent where the declaration is now.
 *
 * <p>The half of the boundary that has to keep working. What a declaration says is answered apart
 * from where it is written so that moving one reaches nobody; a reader that puts a caret under the
 * declaration still means where it is, and it asks for that separately. Left depending on the
 * meaning for both, such a reader would go on pointing at the line the declaration used to be on for
 * as long as it kept saying the same thing — and the report would be wrong in a way no test of what
 * the compiler says can see, because what it says would not have changed.
 *
 * <p>Written now rather than when the cut starts saving work. A check that a caret follows its
 * declaration passes today whatever the reader depends on, and it is the one that would fail the
 * day the answer it depends on stops moving.
 */
class AReportAboutADeclarationFollowsItWhenItMovesTest {

    /** A product with no value: nothing satisfies both of its rules, so it is refused. */
    private static final String EMPTY = """
            module shop.empty exposing ( Impossible )

            data Impossible = Int
                invariant value >= 1 && value <= 0
            """;

    /** A rule another module is judged against, written above a declaration it says nothing about. */
    private static final String RULED = """
            module shop.prices exposing ( Amount )

            data Amount = Int
                invariant value >= 0

            data Note = Int
            """;

    /** The same two declarations, written the other way round. Nothing is added or taken away. */
    private static final String REORDERED = """
            module shop.prices exposing ( Amount )

            data Note = Int

            data Amount = Int
                invariant value >= 0
            """;

    /** Builds one, out of a number nothing here says anything about, so the rule is left standing
     *  and the construction is warned about. */
    private static final String BUILDING = """
            module shop.cart exposing ( make )

            import shop.prices ( Amount )

            behavior make : (n: Int) -> Amount
                constructs Amount
            let make (n) = Amount(n)
            """;

    @Test
    void movingTheDeclarationMovesTheCaretUnderIt() {
        Compilation c = Compilation.ofDocuments(Map.of("empty.sou", EMPTY), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        int before = whereItIsReported(c);

        Map<String, String> edited = new LinkedHashMap<>();
        edited.put("empty.sou", EMPTY.replace("data Impossible",
                "// two lines written above it\n// which move it down the file\ndata Impossible"));
        c.update(edited, Set.of());
        c.answerEverything();

        assertNotEquals(before, whereItIsReported(c),
                "the declaration was written two lines further down and the report still points at"
                        + " the line it used to be on");
        assertEquals(before + 2, whereItIsReported(c),
                "the report followed the declaration, but not to where it went");
    }

    /**
     * A module that imports the declaration is warned about a rule of it, and that warning points at
     * the rule where the rule is now — while the body it is about is not checked again.
     *
     * <p>The two halves of the boundary, held at once. A body judged against an imported rule means
     * what it meant when the rule is written somewhere else, so nothing about it is worked out
     * again; the report it raised says where that rule is, which is somewhere else than it was. A
     * reader depending on one answer for both can satisfy either of these and not the two together —
     * keeping the body keeps the caret where it was, and moving the caret checks the body again.
     *
     * <p>The declarations are written in the other order rather than pushed down the file. Where
     * something stands is which of the things written in the text it is, so a line above it moves
     * nothing and a report would follow it with no question asked of anybody.
     */
    @Test
    void aWarningAboutAnImportedRuleFollowsItWithoutCheckingTheBodyAgain() {
        Compilation c = compiling(RULED);
        Answer<?> judged = c.db().ask(new Bodies.CheckedBehavior("shop.cart", "make"));
        int primary = whereTheWarningIs(c);
        int secondary = whereTheRuleIsQuoted(c);

        edit(c, REORDERED);

        assertSame(judged, c.db().ask(new Bodies.CheckedBehavior("shop.cart", "make")),
                "the rule says what it said, so the body judged against it was not judged again");
        assertEquals(primary, whereTheWarningIs(c),
                "and the warning is still about the construction it was about");
        assertNotEquals(secondary, whereTheRuleIsQuoted(c),
                "the rule was written further down the file and the warning still quotes the line"
                        + " it used to be on");
        assertEquals(secondary + 2, whereTheRuleIsQuoted(c),
                "the warning followed the rule, but not to where it went");
    }

    /** The line the one warning about this workspace puts its caret on. */
    private static int whereTheWarningIs(Compilation c) {
        return c.texts().resolve(theOneWarning(c).primary() instanceof Primary.InSource in
                ? in.place().region().start()
                : fail("the warning is supposed to point at the construction")).line();
    }

    /** The line the one warning about this workspace quotes the rule from. */
    private static int whereTheRuleIsQuoted(Compilation c) {
        List<LabeledRegion> quoted = theOneWarning(c).secondary();
        assertEquals(1, quoted.size(),
                "the warning is supposed to quote the one rule it is about: " + quoted);
        return c.texts().resolve(quoted.getFirst().place() instanceof DiagnosticPlace.InSource in
                ? in.region().start()
                : fail("the rule is written in this workspace and is supposed to be quoted")).line();
    }

    private static Diagnostic theOneWarning(Compilation c) {
        List<Located> warnings = c.warnings();
        assertEquals(1, warnings.size(),
                "this workspace is supposed to be warned about exactly one thing: " + warnings);
        return warnings.getFirst().diagnostic();
    }

    /** The workspace with the declaring module written over, and the importer where it was. */
    private static void edit(Compilation c, String prices) {
        Map<String, String> edited = new LinkedHashMap<>();
        edited.put("prices.sou", prices);
        edited.put("cart.sou", BUILDING);
        c.update(edited, Set.of());
        c.answerEverything();
    }

    private static Compilation compiling(String prices) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("prices.sou", prices);
        byId.put("cart.sou", BUILDING);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertEquals(List.of(), c.errors(), "this workspace is supposed to compile");
        return c;
    }

    /** The line the one report about this workspace puts its caret on. */
    private static int whereItIsReported(Compilation c) {
        List<Located> errors = c.errors();
        assertEquals(1, errors.size(),
                "this workspace is supposed to be refused for exactly one thing: " + errors);
        if (errors.getFirst().diagnostic().primary() instanceof Primary.InSource in) {
            // The line a reader is sent to, which is what the file is laid out as now — the place
            // itself is what the declaration is, and writing above it leaves that where it was.
            return c.texts().resolve(in.place().region().start()).line();
        }
        throw new AssertionError("the report is supposed to point at the declaration, and points "
                + errors.getFirst().diagnostic().primary() + " instead");
    }
}
