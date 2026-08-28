package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That the rules leave an input no value is one fact about the behavior, however many rules and
 * positions it took to be true.
 *
 * <p>Two clauses each admitting values are empty together. Neither of them is the one that failed,
 * and there is no position for it to be about — so a reader sent to look at either is looking at
 * half of a contradiction, and a reader told once per position is told the same thing as many times
 * as the record has fields.
 *
 * <p><b>Which is why the proof is asked for once and read by whoever needs it.</b> The reading of a
 * behavior's input holds every parameter's rules together, and that is the only place a
 * contradiction between two declarations is visible at all. Each measure of that input reads the one
 * answer; asked per measure, two of them could disagree about one model.
 *
 * <p>Not a gap. A gap is a row nobody has written and somebody could; here no row exists to write,
 * so a strict build has nothing to refuse over and no author is being asked for anything.
 */
class AnInputTheRulesLeaveEmptyIsSaidOnceTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * Four positions and two clauses, and the emptiness is in neither clause alone.
     *
     * <p>{@code lo <= hi} and {@code hi < lo} each admit plenty. Together they admit nothing, and
     * the record has four fields for the answer to be said at if anything said it per position.
     */
    private static final String MODEL = """
            module m

            data Box =
                { lo: Int
                , hi: Int
                , name: String
                , tag: String
                }
                invariant ordered = lo <= hi
                invariant reversed = hi < lo

            data Ok

            behavior read : (b: Box) -> Ok
            let read (b) = Ok
            """;

    private record Measured(JsonNode behavior, String human) {}

    private static Measured measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        JsonNode document = JSON.readTree(report.json(SourceNameResolver.identity()));
        return new Measured(document.get("modules").get(0).get("behaviors").get(0),
                report.human(SourceNameResolver.identity()));
    }

    /** The measures of that input are not applicable, and say so for the one reason. */
    @Test
    void everyMeasureOfTheInputReadsTheOneAnswer() {
        JsonNode partition = measured().behavior().path("partition");
        for (String measure : List.of("axesMeasure", "boundariesMeasure")) {
            assertEquals("no_feasible_input",
                    partition.path(measure).path("reason").asString(),
                    measure + " reads the behavior's own answer: " + partition.path(measure));
        }
    }

    /**
     * And the human report says it once, not once per position.
     *
     * <p>The count is the assertion. Four positions and two clauses are what would make a reading
     * that answered per position or per rule say it four times or twice, and a reading that answers
     * once says it once whatever the record holds.
     */
    @Test
    void theReportSaysItOncePerMeasureAndNotOncePerPosition() {
        List<String> said = new ArrayList<>();
        measured().human().lines()
                .filter(line -> line.contains("no_feasible_input"))
                .forEach(said::add);
        assertEquals(2, said.size(),
                "one line per measure of the input, and no more: " + said);
    }

    /** And nothing is owed over it: no row exists to be missing. */
    @Test
    void nothingIsOwedOverAnInputThatHoldsNothing() {
        List<String> kinds = new ArrayList<>();
        measured().behavior().path("findings")
                .forEach(each -> kinds.add(each.path("kind").asString()));
        assertTrue(kinds.stream().noneMatch(kind -> kind.contains("row")),
                "a row nobody can write is not a row nobody has written: " + kinds);
    }
}
