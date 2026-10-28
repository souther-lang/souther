package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An arm of a library operation's copy that the body owes nothing through is no fork of the body's,
 * so the body is asked whether a row tells it apart from answering one value, as a body that calls
 * no such operation is.
 *
 * <p>The copy of {@code List.take} has arms, and a rewrite of one of them is another program. Read
 * as the body's own fork, it kept the body from being asked about the one answer while owing no
 * row of its own, and a single row that ran none of the work passed a strict build.
 */
class ABodyThatCallsALibraryOperationIsAskedAboutOneAnswerTest {

    private static final String MODEL = """
            module repro.withtake

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Throw = List<Pin>
                invariant List.allDistinctBy(p -> p, value)

            behavior points : (t: Throw) -> Int

            let points (t) = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            example points
                | (Throw([])) -> 0
                | (Throw([Pin(12)])) -> 12
                | (Throw([Pin(1), Pin(2)])) -> 2
                | (Throw([Pin(1), Pin(2), Pin(3)])) -> 3

            behavior score : (throws: List<Throw>) -> Int

            let score (throws) = List.fold((acc, t) -> acc + points(t), 0, throws)

            example score
                | ([]) -> 0
                | ([Throw([Pin(12)])]) -> 12
                | ([Throw([Pin(12)]), Throw([Pin(1), Pin(2)])]) -> 14

            behavior running : (throws: List<Throw>) -> List<Int>

            """;

    private static final String ONE_ROW = """

            example running
                | ([]) -> []
            """;

    private static final String A_ROW_THAT_RUNS_THE_WORK = """

            example running
                | ([]) -> []
                | ([Throw([Pin(12)])]) -> [12]
            """;

    private static final String WITH_TAKE =
            "let running (throws) ="
                    + " List.mapIndexed((i, _) -> score(List.take(i, throws)), throws)\n";

    private static final String WITH_TAKE_RIGHT =
            "let running (throws) ="
                    + " List.mapIndexed((i, _) -> score(List.take(i + 1, throws)), throws)\n";

    private static final String WITHOUT_TAKE =
            "let running (throws) = List.mapIndexed((i, _) -> score(throws), throws)\n";

    @Test
    void aBodyCallingTakeIsAskedAboutOneAnswer() {
        Compilation compilation = compiled(MODEL + WITH_TAKE + ONE_ROW);

        assertEquals(1, oneAnswerLines(compilation).size(), () -> page(compilation));
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy(), () -> page(compilation));
    }

    @Test
    void aBodyCallingNoLibraryOperationIsAskedTheSame() {
        Compilation compilation = compiled(MODEL + WITHOUT_TAKE + ONE_ROW);

        assertEquals(1, oneAnswerLines(compilation).size(), () -> page(compilation));
    }

    @Test
    void aRowThatRunsTheWorkTellsTheBodyApartFromOneAnswer() {
        Compilation compilation = compiled(MODEL + WITH_TAKE_RIGHT + A_ROW_THAT_RUNS_THE_WORK);

        assertEquals(List.of(), oneAnswerLines(compilation), () -> page(compilation));
    }

    private static List<String> oneAnswerLines(Compilation compilation) {
        return page(compilation).lines().map(String::strip)
                .filter(line -> line.startsWith("! no row would come out differently")
                        && line.contains("the body always answered"))
                .toList();
    }

    private static String page(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
