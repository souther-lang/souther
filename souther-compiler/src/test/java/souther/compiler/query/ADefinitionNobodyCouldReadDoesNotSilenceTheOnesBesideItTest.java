package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body nobody could read costs that definition its answer, and costs the ones beside it nothing.
 *
 * <p>The desugaring says so of itself: a definition is the unit it answers in, and a module is
 * assembled from all of them. What broke that was the assembly — a definition missing from what it
 * was handed left it with no module to hand over, so the mistake in the next definition was not
 * reported until the compile after this one.
 *
 * <p>Two mistakes in one module, and each is about its own definition. What is held is that both are
 * said.
 */
class ADefinitionNobodyCouldReadDoesNotSilenceTheOnesBesideItTest {

    private static final String SOURCE = """
            module m exposing ( Out, run )

            data Amount = Int
            data Out = { n: Int }

            let bad (a: Int, b: Int) : Int = 0

            behavior run : (n: Int) -> Out constructs Out
            let run (n) = Out { n = "text" }
            """;

    private static List<String> saidOf(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("m.sou", source);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        return c.diagnostics().values().stream().flatMap(List::stream)
                .map(each -> each.diagnostic().code()).toList();
    }

    /** The one beside it on its own, so that what the pair says below can be told from it. */
    @Test
    void theIndependentMistakeIsSaidOnItsOwn() {
        List<String> said = saidOf(SOURCE);

        assertTrue(said.contains("E1317"), "a field given a value of another type: " + said);
    }

    /** And it is still said where a definition beside it holds a newtype applied to two values. */
    @Test
    void theIndependentMistakeIsStillSaidBesideOneNobodyCouldRead() {
        List<String> said = saidOf(SOURCE.replace(
                "let bad (a: Int, b: Int) : Int = 0",
                "let bad (a: Int, b: Int) : Int = Amount(a, b).value"));

        assertTrue(said.contains("E1317"),
                "the definition beside the one nobody could read is checked all the same: " + said);
        assertTrue(said.contains("E1802"),
                "and the one nobody could read is said as what it is — a newtype wrapping a count"
                        + " other than one, rather than a construction written somewhere it may"
                        + " not be: " + said);
    }
}
