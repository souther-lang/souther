package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comparison draws its line wherever the behavior's answer is read off it.
 *
 * <p>One rule written several ways. Naming a truth, answering with it, or putting it in the answer's
 * data are not statements about what a model divides — so a body that compares its input at a value
 * divides it there however the comparison reaches the answer, and a reader that had to find a fork
 * first said of four of these that the model divides their input no way.
 *
 * <p>Measured against the fork spelling rather than against numbers written down here. What they have
 * to agree on is the position and the lines, and an expectation repeated per spelling would go on
 * holding if every one of them fell silent together.
 */
class AComparisonDrawsALineWhereverItsTruthIsReadTest {

    private static final String MODEL = """
            module example.read

            data Temp = Int
            data Cold
            data Hot
            data Verdict = { cold: Bool }

            behavior underAFork : (temp: Temp) -> Cold | Hot
            let underAFork (temp) =
                if temp.value < 240 then Cold else Hot

            behavior namedThenForked : (temp: Temp) -> Cold | Hot
            let namedThenForked (temp) = {
                let cold = temp.value < 240
                if cold then Cold else Hot
            }

            behavior answeredDirectly : (temp: Temp) -> Bool
            let answeredDirectly (temp) = temp.value < 240

            behavior namedThenAnswered : (temp: Temp) -> Bool
            let namedThenAnswered (temp) = {
                let cold = temp.value < 240
                cold
            }

            behavior insideTheAnswersData : (temp: Temp) -> Verdict
            let insideTheAnswersData (temp) =
                Verdict { cold = temp.value < 240 }

            behavior namedAndNeverRead : (temp: Temp) -> Cold
            let namedAndNeverRead (temp) = {
                let cold = temp.value < 240
                Cold
            }

            behavior namedThroughAChainNothingReads : (temp: Temp) -> Cold
            let namedThroughAChainNothingReads (temp) = {
                let cold = temp.value < 240
                let alias = cold
                Cold
            }
            """;

    private static Map<String, PartitionEvidence> measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
    }

    private static List<String> classesOf(PartitionEvidence evidence) {
        return evidence.axes().stream().map(axis -> axis.path() + ": " + axis.classes()).toList();
    }

    private static List<String> linesOf(PartitionEvidence evidence) {
        return BorderAssessment.pointsOf(evidence.boundaries()).stream()
                .filter(p -> p.role().againstTheLine()).filter(p -> p.owed() != null)
                .map(p -> p.label() + " " + p.role())
                .sorted()
                .toList();
    }

    /** The spellings that read the truth somewhere other than a fork's condition. */
    private static final List<String> READ_ELSEWHERE = List.of(
            "namedThenForked", "answeredDirectly", "namedThenAnswered", "insideTheAnswersData");

    /**
     * Every spelling that reads the truth divides what the fork spelling divides.
     *
     * <p>One rule and four uses of it: tested by a fork, given a name a line above the fork that
     * tests it, answered with, and written into a field of the answer's data. Each was reported as a
     * position the model draws no line through, which is not a quieter answer than the fork
     * spelling's — it is the opposite one.
     */
    @Test
    void everySpellingThatReadsTheTruthDividesWhatTheForkSpellingDivides() {
        Map<String, PartitionEvidence> measured = measured();
        PartitionEvidence held = measured.get("underAFork");

        for (String behavior : READ_ELSEWHERE) {
            assertEquals(classesOf(held), classesOf(measured.get(behavior)), behavior);
            assertEquals(linesOf(held), linesOf(measured.get(behavior)), behavior);
        }
    }

    /** And none of them is left among the positions no class came back for. */
    @Test
    void noSpellingThatReadsTheTruthNamesItsInputAsOneNothingDivides() {
        Map<String, PartitionEvidence> measured = measured();
        for (String behavior : READ_ELSEWHERE) {
            assertEquals(List.of(), measured.get(behavior).notDerivable(), behavior);
            assertEquals(List.of(), measured.get(behavior).notRead(), behavior);
        }
    }

    /**
     * A comparison whose truth nothing reads divides nothing.
     *
     * <p>The other half of the same rule, and the half a policy taking every comparison it can
     * measure gets wrong. The answer here is {@code Cold} at every temperature, so a partition at 240
     * would have the report say this behavior distinguishes two ranges of its input that it in fact
     * answers alike — a distinction the model does not draw, asked for as rows.
     */
    @Test
    void aTruthNothingReadsDividesNothing() {
        PartitionEvidence dead = measured().get("namedAndNeverRead");

        assertEquals(List.of(), classesOf(dead));
        assertEquals(List.of(), linesOf(dead));
    }

    /**
     * A truth read only by a name nothing reads still draws its line, and that is where this stops.
     *
     * <p>Written down because it is the limit and not an accident. Which values reach an answer is
     * read in one pass: a name is read where anything reads it, wherever that is written, so a
     * binding read only from inside another binding nothing reads counts as read. Telling those
     * apart is a fixed point over the bindings, and what it would take away is a chain of dead code.
     *
     * <p>The direction is chosen. A line drawn here asks for two rows the behavior answers alike,
     * which an author can see in their own body; the other way round takes a rule of the model out
     * of the report with nothing said, which is the defect the whole of this is about. So this holds
     * the over-reporting in place rather than leaving it to be discovered as a bug — and a reading
     * that closes the chain should replace this expectation rather than being written beside it.
     */
    @Test
    void aTruthReadOnlyThroughADeadChainStillDrawsItsLine() {
        Map<String, PartitionEvidence> measured = measured();

        assertEquals(classesOf(measured.get("underAFork")),
                classesOf(measured.get("namedThroughAChainNothingReads")));
    }
}
