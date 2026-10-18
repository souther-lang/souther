package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A remainder of one number by another the row chooses is a number of its own, and a rule about it
 * is a line on that remainder and on neither number.
 *
 * <p>{@code Int.floorMod(eaches, pack) == 0} relates the two: fixing the divisor leaves a period on
 * the dividend, and the period moves with the divisor. The dividend nought is divisible by every
 * divisor, so nought is a class of the dividend. The divisors one and minus one divide every
 * dividend, which are two single values of one position, and a position keeps one such line.
 */
class ARemainderByAValueTheRowChoosesIsARelationBetweenTheTwoTest {

    @Test
    void theRemainderIsALineAndNoughtIsAClassOfTheDividend() {
        Compilation compilation = compiled("Int.floorMod(eaches, pack) == 0");
        assertTrue(bordersOf(linesOf(compilation)).contains("0"),
                bordersOf(linesOf(compilation)).toString());
        Map<String, List<String>> classes = classesOf(measured(compilation));
        assertEquals(List.of("eaches/= 0", "eaches//= 0"), classes.get("eaches"),
                classes.toString());
        assertTrue(classes.containsKey("pack"), classes.toString());
    }

    /** Written the other way round, the same quantity and the same class. */
    @Test
    void writtenTheOtherWayRoundItIsTheSameRelation() {
        Map<String, List<String>> classes =
                classesOf(measured(compiled("0 == Int.floorMod(eaches, pack)")));
        assertEquals(List.of("eaches/= 0", "eaches//= 0"), classes.get("eaches"),
                classes.toString());
    }

    /**
     * With the divisors every size from two up, the dividends nought and one either side are the
     * values that settle it, and each is a class: the values several of one rule single out at one
     * position are several pieces of evidence.
     */
    @Test
    void severalValuesThatSettleItAreSeveralClassesOfTheDividend() {
        Compilation compilation = compiled("""
                data Pack = Int
                    invariant value >= 2
                """, "eaches: Int, pack: Pack", "Int.floorMod(eaches, pack.value) == 0");
        assertEquals(List.of("eaches/x < -1", "eaches/-1 <= x <= -1", "eaches/-1 < x <= 0",
                        "eaches/0 < x <= 1", "eaches/1 < x"),
                classesOf(measured(compilation)).get("eaches"));
    }

    /** With both signs of divisor, the divisors one and minus one are two classes of the divisor. */
    @Test
    void theTwoDivisorsThatDivideEveryDividendAreTwoClassesOfTheDivisor() {
        Map<String, List<String>> classes = classesOf(measured(compiled(
                "Int.floorMod(eaches, pack) == 0")));
        assertEquals(List.of("pack/= -1", "pack/= 1", "pack//= -1, 1"), classes.get("pack"),
                classes.toString());
    }

    /** A divisor held to exactly two is not every size from some one up: parity decides. */
    @Test
    void aDivisorHeldToTwoLeavesTheDividendNothingToSay() {
        Compilation compilation = compiled("""
                data Pack = Int
                    invariant value == 2
                """, "eaches: Int, pack: Pack", "Int.floorMod(eaches, pack.value) == 0");
        assertTrue(!classesOf(measured(compilation)).containsKey("eaches"));
    }

    /** Arithmetic in the dividend is the run's, in the type: the stop stands. */
    @Test
    void aShiftedDividendIsNotRead() {
        Compilation compilation = compiled("Int.floorMod(eaches + 1, pack) == 0");
        assertEquals(List.of(), bordersOf(linesOf(compilation)));
    }

    /** The remainder takes the divisor's sign, and a divisor of nought has none. */
    @Test
    void theRemainderTakesTheSignOfTheDivisor() {
        assertEquals(Optional.of(ExactRatio.of(2)), remainderOf(-7, 3));
        assertEquals(Optional.of(ExactRatio.of(-2)), remainderOf(7, -3));
        assertEquals(Optional.of(ExactRatio.ZERO), remainderOf(Long.MIN_VALUE, -1));
        assertEquals(Optional.of(ExactRatio.of(-1)), remainderOf(-1, -2));
        assertEquals(Optional.empty(), remainderOf(5, 0));
    }

    private static Optional<ExactRatio> remainderOf(long dividend, long divisor) {
        NumericTerm x = new NumericTerm.ValueOf(TermPath.of("x"));
        NumericTerm y = new NumericTerm.ValueOf(TermPath.of("y"));
        Map<NumericTerm, Place> values = new LinkedHashMap<>();
        values.put(x, Count.of(dividend));
        values.put(y, Count.of(divisor));
        return OrderedAffineBoundary.remainderByAnInputAt(x, y, values)
                instanceof ExactAnswer.Held<Optional<ExactRatio>>(var left) ? left : null;
    }

    private static List<BorderAssessment> linesOf(Compilation compilation) {
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    private static List<String> bordersOf(List<BorderAssessment> lines) {
        return lines.stream().filter(each -> each.axis().contains("floorMod"))
                .map(BorderAssessment::value).toList();
    }

    private static PartitionEvidence measured(Compilation compilation) {
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get("f");
        assertNotNull(evidence, "f was measured");
        return evidence;
    }

    private static Map<String, List<String>> classesOf(PartitionEvidence evidence) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        evidence.axes().forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    private static Compilation compiled(String condition) {
        return compiled("", "eaches: Int, pack: Int", condition);
    }

    private static Compilation compiled(String prelude, String parameters, String condition) {
        String model = """
                module demo

                data Ok
                data No

                %s

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    guard %s else No
                    Ok
                }
                """.formatted(prelude, parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
