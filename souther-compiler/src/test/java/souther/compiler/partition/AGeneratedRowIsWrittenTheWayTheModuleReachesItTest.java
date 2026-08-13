package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A generated row names a type as the module it is offered to reaches it.
 *
 * <p>A row is text somebody pastes into their own module, so the names in it are that module's
 * references and not the declarations' own spellings. One {@code lib.Amount} is {@code Amount} where
 * an import brought it in, {@code up.Amount} where an alias reaches it, and {@code lib.Amount} where
 * neither does — and the generator, which holds the declaration, is the one place that cannot see
 * which (issue #696).
 *
 * <p>Held against the compiler rather than against a spelling written out here. Whether the row is a
 * row is whether it compiles where it is offered, so the row this produces is pasted back into the
 * module it was produced for and the module is compiled again. A test comparing the text with an
 * expected string agrees with whatever the generator does, including writing a name nothing resolves.
 */
class AGeneratedRowIsWrittenTheWayTheModuleReachesItTest {

    private static final String LIB = """
            module lib exposing ( Amount, Kind, Domestic, Overseas )

            data Amount = Int

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas
            """;

    /** A boundary at an imported newtype, drawn by a guard, and a case beside it. */
    private static String app(String imports, String amount, String kind) {
        return """
                module app exposing ( Req, Ok, No, Verdict, f )

                %s

                data Req = { amount: %s, kind: %s }

                data Ok
                data No
                data Verdict = Ok | No

                behavior f : (r: Req) -> Verdict
                    constructs Ok, No
                let f (r) = { guard r.amount.value < 500 else Ok
                    No }
                """.formatted(imports, amount, kind);
    }

    private static Compilation compiled(String source) {
        Compilation compilation =
                Compilation.ofSources(List.of(LIB, source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * The distinct rows this module is offered, boundaries and pairs alike, as the text of the one
     * input each carries.
     *
     * <p>Distinct, and in the order they were offered. How many rows a boundary and a pair each ask
     * for is the generator's own arithmetic and is held where that is what is under test; what is
     * under test here is the names in them, and a row repeated says nothing more about a name than
     * the first one did.
     */
    private static List<String> rowsFor(String source) {
        Map<String, Adequacy.Filling> filling =
                compiled(source).db().ask(new Adequacy.Generated("app")).value();
        Adequacy.Filling f = filling.get("f");
        return java.util.stream.Stream
                .concat(f.boundaries().rows().stream(), f.pairs().rows().stream())
                .map(r -> String.join(", ", r.inputs().stream().map(FixtureTemplate::text).toList()))
                .distinct().toList();
    }

    /** An import that brought the names in: they are written as they are declared. */
    @Test
    void aTypeAnImportBroughtInIsWrittenBare() {
        List<String> rows = rowsFor(app("import lib ( Amount, Kind, Domestic, Overseas )",
                "Amount", "Kind"));

        assertEquals(List.of(
                        "Req { amount = Amount(500), kind = Domestic }",
                        "Req { amount = Amount(499), kind = Domestic }",
                        "Req { amount = Amount(499), kind = Overseas }",
                        "Req { amount = Amount(500), kind = Overseas }"),
                rows);
    }

    /**
     * The same model reaching the same declarations through an alias. Nothing about the types
     * changed and every name in every row did.
     */
    @Test
    void aTypeReachedThroughAnAliasIsWrittenThroughIt() {
        List<String> rows = rowsFor(app("import lib as up", "up.Amount", "up.Kind"));

        assertEquals(List.of(
                        "Req { amount = up.Amount(500), kind = up.Domestic }",
                        "Req { amount = up.Amount(499), kind = up.Domestic }",
                        "Req { amount = up.Amount(499), kind = up.Overseas }",
                        "Req { amount = up.Amount(500), kind = up.Overseas }"),
                rows);
    }

    /**
     * And where the module declares an {@code Amount} of its own beside the one it reaches through
     * the alias, which is the case a bare spelling answers wrong rather than not at all: both names
     * resolve, and only one of them is the type at the position.
     */
    @Test
    void aTypeIsNotWrittenBareWhereTheBareNameIsAnotherDeclaration() {
        List<String> rows = rowsFor(app("import lib as up\n\n                data Amount = String",
                "up.Amount", "up.Kind"));

        assertEquals(List.of(
                        "Req { amount = up.Amount(500), kind = up.Domestic }",
                        "Req { amount = up.Amount(499), kind = up.Domestic }",
                        "Req { amount = up.Amount(499), kind = up.Overseas }",
                        "Req { amount = up.Amount(500), kind = up.Overseas }"),
                rows);
    }

    /**
     * A type the import list left out is written under the module that declares it — beside a case
     * from the same module the same import did bring in, so the two forms stand in one row.
     */
    @Test
    void aTypeAnImportLeftOutIsWrittenUnderItsModule() {
        String source = app("import lib ( Kind, Domestic, Overseas )", "lib.Amount", "Kind");
        List<String> rows = rowsFor(source);

        assertEquals(List.of(
                        "Req { amount = lib.Amount(500), kind = Domestic }",
                        "Req { amount = lib.Amount(499), kind = Domestic }",
                        "Req { amount = lib.Amount(499), kind = Overseas }",
                        "Req { amount = lib.Amount(500), kind = Overseas }"),
                rows);
        assertEquals(List.of("E1905"), addedByPasting(source, rows.get(0)),
                "and the qualified form compiles where it is offered");
    }

    /**
     * And the row compiles where it is offered, which is the whole of what a row being a row means.
     *
     * <p>Pasted back into the module it was written for, and held to every diagnostic the compile
     * reports rather than to the absence of one of them: a row that named nothing out of scope
     * could still be a syntax error or a value of the wrong type, and a check written as "no
     * E1023" would call that a row. What is left is E1905, the expectation this pastes in being
     * deliberately not the one the behavior answers with — the row was read, which is the point.
     *
     * <p>Beside it, the row this used to offer — the same values under the declarations' own
     * spellings — so the check is one this model can fail. The names are the only difference
     * between the two, and one of them is two names out of scope in the module both are pasted
     * into.
     */
    @Test
    void aRowCompilesInTheModuleItIsOfferedToAndTheDeclarationsOwnSpellingDoesNot() {
        String source = app("import lib as up", "up.Amount", "up.Kind");
        String offered = rowsFor(source).get(0);
        String declared = offered.replace("up.", "");

        assertEquals(List.of("E1905"), addedByPasting(source, offered),
                "the row was read, and only the expectation pasted beside it disagrees");
        assertEquals(List.of("E1023", "E1023"), addedByPasting(source, declared),
                "and the declarations' own spellings are two names that are not in scope here");
    }

    /**
     * What pasting {@code row} into {@code source} adds to what that model already reported.
     *
     * <p>The difference and not the whole, because a model can have something to say without the
     * row — one of these leaves an import it does not use — and what is under test is the row. Held
     * as everything the compile added rather than as the absence of one code: a row that named
     * nothing out of scope could still be a syntax error or a value of the wrong type, and a check
     * written as "no E1023" would call that a row.
     */
    private static List<String> addedByPasting(String source, String row) {
        List<String> before = new java.util.ArrayList<>(codesFor(source));
        List<String> added = new java.util.ArrayList<>();
        for (String each : codesFor(source + """

                example f
                    | "boundary" : (%s) -> No
                """.formatted(row))) {
            if (!before.remove(each)) {
                added.add(each);
            }
        }
        return added;
    }

    /** Every diagnostic a compile of {@code source} reports. */
    private static List<String> codesFor(String source) {
        return compiled(source).diagnostics().values().stream().flatMap(List::stream)
                .map(d -> d.diagnostic().code()).toList();
    }
}
