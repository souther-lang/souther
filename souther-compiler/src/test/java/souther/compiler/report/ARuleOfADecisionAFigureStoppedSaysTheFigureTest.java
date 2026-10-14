package souther.compiler.report;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule of a decision whose search a figure of this compiler's stopped is said with the figure,
 * on the page and in the document.
 *
 * <p>The arm through {@code case Some} needs a value of a type whose rule asks for more than a
 * proposal holds. Said with no figure, the rule reads as one nothing could compose a row for, and
 * an author is not told that a number this compiler holds is what stopped it, nor which.
 *
 * <p>For a string and for a list, because they meet different figures, and each beside the same
 * model one short of its figure, where the rule is composed for and nothing is said of it.
 */
class ARuleOfADecisionAFigureStoppedSaysTheFigureTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module p

            data Big = %s
                invariant %s(value) >= %d
            data R = { o: Option<Big> }

            behavior a : (r: R) -> Int
            let a (r) =
                match r.o with
                    | Some v -> 1
                    | None -> 0
            """;

    private static final int CHARACTERS = CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS.maximum();

    private static final int ELEMENTS = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.maximum();

    private static String aString(int atLeast) {
        return MODEL.formatted("String", "String.length", atLeast);
    }

    private static String aList(int atLeast) {
        return MODEL.formatted("List<Bool>", "List.length", atLeast);
    }

    @Test
    void aStringPastTheFigureIsSaidToBeStoppedThere() {
        assertSaysTheFigure(aString(CHARACTERS + 1),
                CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS);
    }

    @Test
    void aListPastTheFigureIsSaidToBeStoppedThere() {
        assertSaysTheFigure(aList(ELEMENTS + 1), CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS);
    }

    /** At the figure, a value is built and the rule is not one nothing could compose a row for. */
    @Test
    void atTheFigureTheRuleIsComposedFor() {
        for (String model : List.of(aString(CHARACTERS), aList(ELEMENTS))) {
            Compilation compilation = measured(model);
            AdequacyReport report = AdequacyReport.of(compilation);
            String page = human(report);

            assertEquals(List.of(), ruleLines(page), () -> "a value of Big is built here: " + page);
            assertEquals(List.of(), shortfalls(report, compilation),
                    "and the document has no shortfall to say of the rule");
        }
    }

    private static void assertSaysTheFigure(String model, CompositionBudget figure) {
        Compilation compilation = measured(model);
        AdequacyReport report = AdequacyReport.of(compilation);
        String page = human(report);
        List<String> lines = ruleLines(page);

        assertEquals(1, lines.size(), () -> "the rule through case Some is the one: " + page);
        assertTrue(lines.get(0).contains(Reasons.met(CompositionShortfall.of(Set.of(figure)))),
                () -> "the rule's own line opens on the figure its search stopped at: "
                        + lines.get(0));

        List<JsonNode> said = shortfalls(report, compilation);
        assertEquals(1, said.size(), () -> "one word the search came back with: " + said);
        List<String> figures = new ArrayList<>();
        JsonNode written = said.get(0).get("figures");
        if (written != null) {
            written.forEach(each -> figures.add(each.asString()));
        }
        assertEquals(List.of(AdequacyReport.word(figure)), figures,
                () -> "and the document says the same figure beside the word: " + said);
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** The page of a report, which is built once per compilation and read twice. */
    private static String human(AdequacyReport report) {
        return report.human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** The lines the page says a rule of the decision nothing could show a row for in. */
    private static List<String> ruleLines(String page) {
        return page.lines()
                .filter(line -> line.contains("nothing could show a row can be written at a"
                        + " decision rule"))
                .toList();
    }

    /** Every word the document says a rule's search came back with, over every rule. */
    private static List<JsonNode> shortfalls(AdequacyReport report, Compilation compilation) {
        JsonNode behaviors = JSON.readTree(report
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors");
        List<JsonNode> found = new ArrayList<>();
        behaviors.forEach(behavior -> behavior.get("decision").get("obligations").forEach(rule -> {
            JsonNode words = rule.get("synthesisShortfalls");
            if (words != null) {
                words.forEach(found::add);
            }
        }));
        return found;
    }
}
