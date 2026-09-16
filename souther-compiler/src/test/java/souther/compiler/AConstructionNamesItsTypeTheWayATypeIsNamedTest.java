package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;
import souther.compiler.diag.Severity;
import souther.compiler.fmt.Formatter;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A construction names its type the way a type is named anywhere.
 *
 * <p>Bare, through an alias, or through the module that declares it. Which spellings reach a type
 * is settled once ({@code TypeReachName}) and is what every other position takes — a type position,
 * a binding pattern, a {@code match} arm, a {@code constructs} clause — and a construction was the
 * one place that took only the first of them. So a module that can say which of two {@code Amount}s
 * it means wherever it names one could not say it where it builds one.
 *
 * <p>What is held is that the three are one construction and not three readings of one. They are
 * written against the same declared type in one module, so a spelling that reached something else
 * would not typecheck; and each is formatted and read back, because a spelling the grammar has no
 * reading of does not come back from a format as what went in.
 */
class AConstructionNamesItsTypeTheWayATypeIsNamedTest {

    private static final String DECLARING = """
            module example.parts exposing ( Thing )

            data Thing = { n: Int }
            """;

    /** One module writing the same construction three ways. The import brings the bare name in and
     *  names the module, and the qualified form needs neither. */
    private static final String CARRYING = """
            module example.carrying

            import example.parts as Parts ( Thing )

            data Ok = { n: Int }

            behavior take : (n: Int) -> Ok
                constructs Ok

            let take (n) = Ok { n = n }

            let bare: Thing = Thing { n = 0 }
            let byAlias: Thing = Parts.Thing { n = 1 }
            let byModule: Thing = example.parts.Thing { n = 2 }
            """;

    @Test
    void theThreeSpellingsAreOneConstruction() {
        assertEquals(List.of(), errorsIn(CARRYING),
                "a type is named the same way where one is built as where one is written");
    }

    /**
     * And each comes back from a format as what went in.
     *
     * <p>Read back rather than compared against a written-out expectation. What this is about is
     * that the whole of the construction survives the round trip: a grammar with no reading of the
     * head keeps the name and loses the braces, and a text that lost them is still a text.
     */
    @Test
    void eachSpellingSurvivesBeingFormattedAndReadBack() {
        String formatted = Formatter.format(CARRYING);

        assertEquals(List.of(), CstParser.parse(formatted).errors(),
                () -> "what the formatter wrote parses:\n" + formatted);
        assertEquals(List.of(), errorsIn(formatted),
                () -> "and is the same module:\n" + formatted);
        assertEquals(formatted, Formatter.format(formatted), "and formatting it again moves nothing");
    }

    /** What this compiler refuses {@code carrying} over, which is nothing where it compiles. */
    private static List<String> errorsIn(String carrying) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("parts.sou", DECLARING);
        byId.put("carrying.sou", carrying);
        Compilation compilation = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        compilation.answerEverything();
        List<String> out = new ArrayList<>();
        compilation.diagnostics().forEach((_, said) -> said.forEach(each -> {
            if (each.diagnostic().severity() == Severity.ERROR) {
                out.add(String.valueOf(each.diagnostic().code()));
            }
        }));
        return out;
    }
}
