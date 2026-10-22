package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A rule whose statement was not read because the reading reached a figure says which figure, in
 * the report and in the document.
 *
 * <p>The word both surfaces write for it is the same whichever figure was reached — a part of what
 * it states was not read — and more than one figure stops the reading of what one condition
 * states under that word: how many times it is read along one way and how many times in all, held
 * here, and how many parts one step of the reading comes to. A reader told only the word has no
 * figure to raise, and the one a wider run would have to allow is a different one for each of the
 * models here.
 *
 * <p>Asked of the whole line and the whole entry rather than of the reason underneath, because the
 * reason already carries its figure and what went missing was the report saying it.
 */
class AReadingStoppedAtAFigureSaysWhichFigureTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String THE_WORD = "a part of what it states was not read";

    /** A behavior forking on {@code condition} over a window of months. */
    private static final String FORKING_ON = """
            module m

            data Month = { days: Int }
            data Window = { first: Month, n: Int }

            behavior f : (w: Window) -> Int
            let f (w) = if %s then 1 else 0
            """;

    /** One value more than one condition is read once for along one way. */
    @Test
    void moreValuesThanOneConditionIsReadForNameThatFigure() {
        int most = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        assertNamed(FORKING_ON.formatted("List.any(x -> w.n == x, " + values(most + 1) + ")"),
                CompositionBudget.READINGS_OF_ONE_CONDITION);
    }

    /**
     * Cases compared with cases, each side within what one way reads and the two together past
     * what one condition is read in all: {@code n} cases a side are read {@code 2(n² - 1)} times.
     */
    @Test
    void moreReadingsInAllThanOneConditionMakesNameThatFigure() {
        int side = (int) Math.sqrt(
                CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION.maximum() / 2 + 1) + 1;
        assertNamed(FORKING_ON.formatted(choices("w.n", side) + " > "
                        + choices("w.first.days", side)),
                CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION);
    }

    /**
     * Every rule {@code model} says was not read under {@link #THE_WORD} names {@code figure} and
     * nothing else: on the report's line, on the document's {@code notRead} entry, and on the
     * {@code stopped} entry of the question it leaves standing.
     */
    private static void assertNamed(String model, CompositionBudget figure) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        AdequacyReport report = AdequacyReport.of(compilation);
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());

        String human = report.human(rendering);
        String said = ", stopped at " + figure.counts() + " (" + figure.name() + ", "
                + figure.maximum() + ")";
        List<String> lines = human.lines()
                .filter(line -> line.contains(": " + THE_WORD)
                        || line.contains("— " + THE_WORD))
                .toList();
        assertFalse(lines.isEmpty(), () -> "the model stops a reading under the word: " + human);
        List<String> unnamed = lines.stream().filter(line -> !line.contains(THE_WORD + said))
                .toList();
        assertEquals(List.of(), unnamed, "every line saying the word names " + figure);

        JsonNode document = JSON.readTree(report.json(rendering));
        EveryObjectThisWritesIsShapedTheWayTheSchemaSaysTest.assertShapedLikeTheSchema(document);
        JsonNode partition = document.get("modules").get(0).get("behaviors").get(0)
                .get("partition");
        List<JsonNode> notRead = new ArrayList<>();
        for (JsonNode each : partition.get("notRead")) {
            if (each.get("reason").asString().equals("rule_meaning_not_read")) {
                notRead.add(each);
            }
        }
        List<JsonNode> stopped = new ArrayList<>();
        for (JsonNode question : partition.get("unanswered")) {
            if (question.has("stopped")) {
                for (JsonNode each : question.get("stopped")) {
                    if (each.get("reason").asString().equals("rule_meaning_not_read")) {
                        stopped.add(each);
                    }
                }
            }
        }
        assertFalse(notRead.isEmpty(), () -> "a rule is not read under the word: " + partition);
        assertFalse(stopped.isEmpty(), () -> "a question stands on the word: " + partition);
        List<JsonNode> entries = new ArrayList<>(notRead);
        entries.addAll(stopped);
        String word = AdequacyReport.word(figure);
        List<String> wrong = new ArrayList<>();
        for (JsonNode each : entries) {
            if (!List.of(word).equals(figuresOf(each))) {
                wrong.add(each.toString());
            }
        }
        assertEquals(List.of(), wrong, "every entry saying the word names " + word);
    }

    private static List<String> figuresOf(JsonNode entry) {
        List<String> out = new ArrayList<>();
        if (entry.has("figures")) {
            entry.get("figures").forEach(each -> out.add(each.asString()));
        }
        return out;
    }

    /** {@code [0, 1, ..., count - 1]}. */
    private static String values(int count) {
        return IntStream.range(0, count).mapToObj(String::valueOf)
                .collect(Collectors.joining(", ", "[", "]"));
    }

    /** A value chosen by {@code count} cases of {@code subject}. */
    private static String choices(String subject, int count) {
        StringBuilder out = new StringBuilder("(");
        for (int at = 1; at < count; at++) {
            out.append("if ").append(subject).append(" == ").append(at).append(" then ")
                    .append(at).append(" else ");
        }
        return out.append("0)").toString();
    }
}
