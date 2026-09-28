package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What one body's check found is said whether or not the body beside it came out.
 *
 * <p>Two bodies are two answers, so a mistake in one is not an account of the other. An author
 * looking at a file with one error in it is reading the whole file, and a warning about a
 * construction further down is about the construction further down.
 *
 * <p>Held because what says a warning is a question about the module and what finds one is a
 * question about a body. The question that says them walks the bodies of the module and has each
 * one's findings to read; a body whose check did not come out has none, which is not an answer about
 * the ones beside it. Written so that reading them body by body cannot quietly become reading them
 * only where every body came out.
 */
class AWarningIsSaidWhateverTheBodyBesideItCameToTest {

    private static final String RULED = """
            module shop.prices exposing ( Amount )

            data Amount = Int
                invariant value >= 0
            """;

    /** One body warned about, and one the check cannot type at all. */
    private static final String TWO_BODIES = """
            module shop.cart exposing ( make, counted )

            import shop.prices ( Amount )

            behavior make : (n: Int) -> Amount
                constructs Amount
            let make (n) = Amount(n)

            behavior counted : (n: Int) -> Int
            let counted (n) = n.nothingIsCalledThis
            """;

    /** The same file with the body that does not type taken out. */
    private static final String ONE_BODY = """
            module shop.cart exposing ( make )

            import shop.prices ( Amount )

            behavior make : (n: Int) -> Amount
                constructs Amount
            let make (n) = Amount(n)
            """;

    @Test
    void theWarningIsSaidBesideAnErrorInTheBodyUnderIt() {
        // What there is to say about this construction, said of the file that has nothing else
        // wrong with it. Named rather than counted, so that the comparison below is between one
        // warning and the same warning.
        assertEquals(List.of("E2011"), codesWarnedAbout(ONE_BODY),
                "the construction this is about is supposed to be warned about on its own");

        assertEquals(List.of("E2011"), codesWarnedAbout(TWO_BODIES),
                "and it stops being warned about once the behavior under it does not type");
    }

    /** The control: the workspace with two bodies really is refused, so the assertion above is
     *  about a module that did not come out and not about a second clean one. */
    @Test
    void andTheWorkspaceWithBothReallyIsRefused() {
        assertEquals(List.of(), errorCodesOf(ONE_BODY), "one body, and nothing wrong with it");
        assertEquals(1, errorCodesOf(TWO_BODIES).size(),
                "two bodies, one of which names nothing: " + errorCodesOf(TWO_BODIES));
    }

    private static List<String> codesWarnedAbout(String importing) {
        return compiled(importing).warnings().stream().map(w -> w.diagnostic().code()).sorted()
                .toList();
    }

    private static List<String> errorCodesOf(String importing) {
        return compiled(importing).errors().stream().map(e -> e.diagnostic().code()).sorted()
                .toList();
    }

    private static Compilation compiled(String importing) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("prices.sou", RULED);
        byId.put("cart.sou", importing);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c;
    }
}
