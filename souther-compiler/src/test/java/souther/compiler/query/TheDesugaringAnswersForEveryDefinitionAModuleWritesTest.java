package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.meta.ModulePath;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The desugaring answers for every definition a module writes.
 *
 * <p>It is a rewrite and not a check. What it turns into a construction is a newtype applied to one
 * value; an application of one to any other count is not a construction of it and is left as the
 * application it is, to be said where the check reads it. So there is no body it comes back with
 * nothing for.
 *
 * <p>Which is what the module above it rests on. A module is assembled from every definition, so a
 * definition with no answer left the ones beside it with no reading either — and the mistake in the
 * next one was not reported until the compile after this. Written as the totality rather than as
 * "the failure is owned per definition", because the failure is not the desugaring's to own.
 */
class TheDesugaringAnswersForEveryDefinitionAModuleWritesTest {

    /** `f` applies a newtype to two values; `g` is written about nothing to do with it. */
    private static final String SOURCE = """
            module m.a exposing ( Amount, f, g )

            data Amount = Int

            behavior f : (n: Int) -> Int
            let f (n) = Amount(n, n).value

            behavior g : (n: Int) -> Int
            let g (n) = n
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", SOURCE);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    /** Both definitions are answered for, the one holding the application among them. */
    @Test
    void everyDefinitionIsAnsweredForWhateverItsBodyHolds() {
        Map<String, souther.compiler.check.Desugared.Fn> fns =
                compiled().db().ask(new Shapes.DesugaredFns("m.a")).value();

        assertTrue(fns.containsKey("f"),
                "the rewrite leaves what is not a construction as it was, and answers");
        assertTrue(fns.containsKey("g"), "and the definition beside it likewise");
    }

    /** So the module is assembled, and the definitions beside the mistake are checked. */
    @Test
    void theModuleIsAssembledAndTheMistakeIsSaidWhereItIsRead() {
        Compilation c = compiled();

        assertTrue(c.db().ask(new Shapes.Desugared("m.a")).present(),
                "every definition was answered for, so there is a module");

        c.answerEverything();
        assertEquals(java.util.List.of("E1802"),
                c.diagnostics().values().stream().flatMap(java.util.List::stream)
                        .map(each -> each.diagnostic().code()).toList(),
                "and the application is said as a newtype wrapping a count other than one, once");
    }
}
