package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.test.ClosedWorldContract;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who may ask an exact number for its digits, and who may take a number an operation was to answer
 * as held.
 *
 * <p>An exact ratio is held as its factors so that no step pays for the digits, and the answer to
 * an operation on one may have no representation at all. Two doors let that reach a reader as an
 * exception: asking for the digits of a number a host holds no place for, and taking an unheld
 * answer as though it were held. Both are shut to reasoning, and open only where the caller has
 * already said why the answer is there.
 *
 * <ul>
 *   <li>{@code asFraction()} writes both numbers out and throws where the host has no place for them.
 *       Only {@link ExactRatio} spells with it, after asking whether the spelling is short;
 *       everything that reasons asks {@code wholeNumber()}, which answers.
 *   <li>{@code wholeNumber()} is asked where a whole number is a modulus, and its answer is
 *       widened where it is unheld.
 *   <li>{@code orFail(...)} takes an unheld answer as a defect of whoever should have refused it.
 *       That is a claim about an earlier place, and it is held here to the callers whose earlier
 *       place is known: a line is refused where lines are drawn, and a form a library declares is
 *       one no model wrote.
 * </ul>
 *
 * <p>Compared whole and not counted, so that one name dropped and another added is the edit this
 * says something about.
 */
@ClosedWorldContract
class WhoMayAskAnExactNumberForItsDigitsOrForAnAnswerItMustHoldTest {

    private static final Pattern ITS_DIGITS = Pattern.compile("\\.asFraction\\(\\)");
    private static final Pattern A_WHOLE_NUMBER = Pattern.compile("\\.wholeNumber\\(\\)");
    private static final Pattern AN_ANSWER_TAKEN_AS_HELD = Pattern.compile("\\.orFail\\(");

    @Test
    void onlyTheSpellingOfANumberAsksForItsDigits() throws IOException {
        // The spelling is in ExactRatio itself, after it has asked whether the digits are few, so
        // the callers that matter are the ones outside it.
        assertEquals(List.of(), callersOf(ITS_DIGITS, "numeric/ExactRatio.java"),
                "a step that reasons asks wholeNumber, which answers where the host holds no place");
    }

    @Test
    void aWholeNumberIsAskedForOnlyWhereItIsAModulus() throws IOException {
        assertEquals(List.of("numeric/AdditiveImage.java", "numeric/AffinePreimage.java"),
                callersOf(A_WHOLE_NUMBER, "numeric/ExactRatio.java"));
    }

    @Test
    void anUnheldAnswerIsTakenAsHeldOnlyWhereAnEarlierPlaceRefusedIt() throws IOException {
        assertEquals(List.of(
                        // The coefficients of a form a library declares, which no model writes.
                        "check/OperationFactBinder.java",
                        // A line is refused where lines are drawn (Cutting), so what reads one
                        // afterwards divides numbers already shown to be held. Its seam is asked
                        // where the comparison is assessed, and a line whose sides were not worked
                        // out is assessed as unread and never reaches the geometry as a line on a
                        // position.
                        "partition/ComparisonGeometry.java",
                        "partition/CutPosition.java",
                        // A level of the quantity asked for its place is one a caller holding a
                        // level of a carrier has established: every reader of it is handed levels
                        // its producer built on the carrier, and a level of the quantity reaching
                        // one is this compiler having mixed two orders.
                        "partition/Level.java",
                        // A line beside a border is named only for a boundary the search drew,
                        // which is drawn only from a seam that was worked out.
                        "query/Settlements.java"),
                callersOf(AN_ANSWER_TAKEN_AS_HELD, "numeric/ExactAnswer.java"));
    }

    /** The production files that call it, other than the one that defines it. */
    private static List<String> callersOf(Pattern call, String definedIn) throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        assertTrue(Files.isDirectory(main), () -> "no " + main.toAbsolutePath());
        Set<String> reading = new LinkedHashSet<>();
        try (Stream<Path> walk = Files.walk(main)) {
            List<Path> sources = walk.filter(each -> each.toString().endsWith(".java")).sorted()
                    .toList();
            assertTrue(sources.size() > 100, () -> "that is not the compiler: " + sources.size());
            for (Path source : sources) {
                if (call.matcher(Files.readString(source)).find()
                        && !relative(source).equals(definedIn)) {
                    reading.add(relative(source));
                }
            }
        }
        return reading.stream().sorted().toList();
    }

    private static String relative(Path source) {
        String path = source.toString().replace('\\', '/');
        return path.substring(path.indexOf("souther/compiler/") + "souther/compiler/".length());
    }
}
