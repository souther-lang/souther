package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of what a fold works out over a list is reached at totals away from the seed, though
 * every element of the list is one the element type allows and the plain value of it adds nothing.
 *
 * <p>The candidates write a list at one size with its elements alike, which reaches a total only
 * at a multiple of the plain value. A point past that is reached by a row beside the ones that
 * ran: the list with an element put in it or changed for one a row of the module ran, whose run
 * the point is read off.
 */
class AComparisonOverWhatAFoldWorksOutIsReachedAwayFromTheSeedTest {

    private static String scorer(int least, int target) {
        return """
                module m

                data Points = Int
                    invariant value >= %d && value <= 12

                data Score = Int
                    invariant value >= 0 && value <= 50

                behavior add : (s: Score, p: Points) -> Score

                let add (s, p) = {
                    let t = s.value + p.value
                    if t > 50 then Score(25) else Score(t)
                }

                example add
                    | (Score(48), Points(3)) -> Score(25)
                    | (Score(48), Points(2)) -> Score(50)
                    | (Score(0), Points(%d)) -> Score(%d)
                    | (Score(40), Points(12)) -> Score(25)
                    | (Score(38), Points(12)) -> Score(50)
                    | (Score(25), Points(10)) -> Score(35)
                    | (Score(49), Points(1)) -> Score(50)

                behavior total : (ps: List<Points>) -> Score

                let total (ps) = List.fold((s, p) -> add(s, p), Score(0), ps)

                example total
                    | ([]) -> Score(0)

                behavior reached : (ps: List<Points>) -> Bool

                let reached (ps) = total(ps).value == %d

                example reached
                    | ([]) -> false
                """.formatted(least, least, least, target);
    }

    private static List<String> openPointsOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        List<String> lines = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList();
        int from = IntStream.range(0, lines.size())
                .filter(at -> lines.get(at).startsWith(behavior + " ")
                        && lines.get(at).contains("implemented"))
                .findFirst().orElseThrow();
        return lines.subList(from + 1, lines.size()).stream()
                .takeWhile(line -> !line.contains("implemented") && !line.startsWith("declarations"))
                .filter(line -> line.startsWith("? nothing could show a row can be written"))
                .toList();
    }

    /** Totals of twenty, one either side, and past it are reached by rows of unlike elements. */
    @Test
    void everyPointOfATotalAwayFromTheSeedIsReached() {
        assertEquals(List.of(), openPointsOf(scorer(0, 20), "reached"));
    }

    /**
     * A total that needs more elements than the rows beside the candidates come to stays open, and
     * is not said to be unreachable: the report names the rows that were made.
     */
    @Test
    void aPointPastTheRowsBesideIsOpenAndSaysWhatWasMade() {
        List<String> open = openPointsOf(scorer(0, 50), "reached");
        assertTrue(!open.isEmpty(), open.toString());
        assertTrue(open.stream().allMatch(line -> line.contains("then rows beside those")), open.toString());
    }

    /** A least of one for the element makes a total of eight a row of unlike elements too. */
    @Test
    void aTotalMoreThanTheSizesTheCandidatesWriteIsReached() {
        assertEquals(List.of(), openPointsOf(scorer(1, 8), "reached"));
    }
}
