package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What happens to the rest of a module when the signatures of the behaviors it injects cannot be
 * built.
 *
 * <p>{@link Bodies.ReqSigs} answers with nothing injected rather than with nothing at all, because a
 * helper's parameter types are settled from those signatures and stopping there would leave every
 * helper in the module undetermined on top of the real error. That is a recovery, and a recovery has
 * to say how far it goes: the mistake is reported where it is, once; no body reports being unable to
 * see what is already known missing; and nothing is emitted.
 */
class ASignatureThatDoesNotBuildTest {

    /** `fetch` is an injection target — no `let` — and its output names a primitive beside a data,
     * which is not a union a behavior can have. `use` requires it and calls it. */
    private static final String SOURCE = """
            module m.a exposing ( A )

            data A = Int

            behavior fetch : (a: A) -> List<Int> | A

            behavior use : (a: A) -> A
                depends on fetch
            let use (a, fetch) = fetch(a)
            """;

    private static Compilation compiled() {
        Compilation c = Compilation.ofDocuments(Map.of("a.sou", SOURCE), Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c;
    }

    @Test
    void theSignatureIsReportedAndNothingElseIs() {
        List<Db.Found> found = compiled().db().allReports();

        assertEquals(1, found.size(), "one signature that does not build, one diagnostic: " + found);
        assertEquals("type.not-a-union-member", found.get(0).report().diagnostic().messageKey());
    }

    @Test
    void theModuleIsNotEmitted() {
        assertNull(compiled().db().ask(new Output.Classes("m.a")).value(),
                "a module whose injected signatures did not build has no meaning to emit");
    }
}
