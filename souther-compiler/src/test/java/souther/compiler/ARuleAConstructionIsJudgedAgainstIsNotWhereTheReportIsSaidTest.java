package souther.compiler;

import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An invariant declared in one module and a construction written in another, compiled together.
 *
 * <p>The invariant is the rule the construction is judged against, and the report is about the
 * construction: E2010 says the value being built is one the invariant rejects, and E2011 that the
 * nothing known there establishes it. Neither says anything is wrong with the invariant, so the file it is
 * declared in gets no marker — the clause is pointed at because a reader needs to see what was not
 * met, which is a different thing from the problem being written there.
 *
 * <p>Worth pinning because the library case is the one that shows what it costs to get wrong: an
 * error on a correct line of a file whose author has nothing to fix, once for every construction in
 * every module that imports it.
 */
class ARuleAConstructionIsJudgedAgainstIsNotWhereTheReportIsSaidTest {

    private static final String LIBRARY = """
            module lib exposing ( Money )
            data Money = Decimal
                invariant nonNegative = value >= 0m
            """;

    /** A value the invariant refuses whatever the path: E2010, an error. */
    private static final String REFUTING = """
            module app
            import lib ( Money )
            behavior calc : (m: Money) -> Money constructs Money
            let calc (m) = Money(0m) - Money(1m)
            """;

    /** A value nothing here establishes the invariant for: E2011, a warning. */
    private static final String UNPROVEN = """
            module app
            import lib ( Money )
            behavior of : (d: Decimal) -> Money constructs Money
            let of (d) = Money(d)
            """;

    private static Map<SourceId, List<Located>> compiled(String app) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("lib.sou", LIBRARY);
        byId.put("app.sou", app);
        return Compiler.diagnoseModules(byId);
    }

    private static List<String> codesOn(Map<SourceId, List<Located>> found, String file) {
        return found.get(new SourceId(file)).stream().map(l -> l.diagnostic().code()).toList();
    }

    @Test
    void aRefutedConstructionIsSaidWhereItIsBuilt() {
        assertEquals(List.of("E2010"), codesOn(compiled(REFUTING), "app.sou"));
    }

    @Test
    void theLibraryDeclaringTheInvariantIsToldNothingAboutARefutedConstruction() {
        Map<SourceId, List<Located>> found = compiled(REFUTING);

        assertEquals(List.of(), codesOn(found, "lib.sou"),
                "the invariant is what the value was judged against, and it is not in the wrong");
    }

    @Test
    void anUnprovenConstructionIsSaidWhereItIsBuilt() {
        assertEquals(List.of("E2011"), codesOn(compiled(UNPROVEN), "app.sou"));
    }

    @Test
    void theLibraryDeclaringTheInvariantIsToldNothingAboutAnUnprovenConstruction() {
        assertEquals(List.of(), codesOn(compiled(UNPROVEN), "lib.sou"));
    }

    /** The clause is still pointed at: a reader has to see what was not met. Not published there,
     *  and shown there — the two are separate questions. */
    @Test
    void theClauseIsStillPointedAtFromTheFileTheReportIsSaidIn() {
        Diagnostic said = compiled(REFUTING).get(new SourceId("app.sou")).get(0).diagnostic();

        assertTrue(said.secondary().stream()
                        .anyMatch(l -> l.place() instanceof souther.compiler.diag.DiagnosticPlace.InSource in
                                && in.region().start().isIn(new SourceId("lib.sou"))),
                "the report points at the clause in the library: " + said.secondary());
    }
}
