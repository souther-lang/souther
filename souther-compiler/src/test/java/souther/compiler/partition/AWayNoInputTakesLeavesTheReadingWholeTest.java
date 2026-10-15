package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Severity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A way proved to be taken by no input is dropped from the reading, and the reading stays whole.
 *
 * <p>The ways out of a node are one for each way its own conditions come out, so between them they
 * take every input the declarations hold. A proof is had of what the declarations hold, so it drops
 * a way some input could have taken only where no declared input is left — and a body that names a
 * type with no value is refused before anything reads it. A node every way out of which a proof
 * dropped would read as one the naming would not hold apart, and the reading of the body as stopped
 * at a figure; the cases here are the ones nearest that, and each stays whole.
 *
 * <p>Two conditions on one line are where a proof is easiest to get wrong: whether the second can
 * still come out the other way depends on what lies between the two, and the reading has to keep
 * the way exactly where something does.
 */
class AWayNoInputTakesLeavesTheReadingWholeTest {

    @Test
    void everyWayIntoAnArmProvedLeavesTheBodyWhole() {
        DecisionReading read = DecisionReadings.of("""
                module demo
                behavior f : (x: Int) -> Int
                let f (x) = if x > 10 then (if x < 5 then 1 else 2) else 3
                """, "f");

        assertEquals(new DecisionReading.Enumeration.Complete(), read.enumeration(),
                "the arm below 5 is reached by no input, and the body is read to its end");
        assertEquals(1, read.impossible().size(), () -> "the one way: " + read.impossible());
        assertEquals(2, read.rules().size(), () -> "and the two ways past it: " + read.rules());
    }

    @Test
    void aWayProvedOnBothSidesOfAnAndLeavesTheBodyWhole() {
        DecisionReading read = DecisionReadings.of("""
                module demo
                behavior f : (x: Int) -> Int
                let f (x) = if x > 10 && x < 5 then 1 else 2
                """, "f");

        assertEquals(new DecisionReading.Enumeration.Complete(), read.enumeration(),
                "the side on which both hold is taken by no input, and the other side is");
        assertEquals(1, read.impossible().size(), () -> "the one way: " + read.impossible());
    }

    @Test
    void twoLinesTheIntegersBetweenThemCannotStandOnAreOne() {
        DecisionReading read = DecisionReadings.of("""
                module demo
                behavior f : (x: Int) -> Int
                let f (x) = if x >= 1 then (if x > 0 then 1 else 2) else 3
                """, "f");

        assertEquals(new DecisionReading.Enumeration.Complete(), read.enumeration());
        assertEquals(1, read.impossible().size(),
                () -> "no integer is at or above 1 and at or below 0: " + read.impossible());
    }

    @Test
    void twoLinesAnIntegerStandsBetweenAreTwoBorders() {
        DecisionReading read = DecisionReadings.of("""
                module demo
                behavior f : (x: Int) -> Int
                let f (x) = if x >= 0 then (if x > 0 then 1 else 2) else 3
                """, "f");

        assertEquals(new DecisionReading.Enumeration.Complete(), read.enumeration());
        assertEquals(List.of(), read.impossible(), "0 takes the way to 2");
        assertEquals(3, read.rules().size(), () -> "every way is a rule: " + read.rules());
    }

    @Test
    void linesThatMeetWhereTheDeclarationsHoldADifferenceAtNoughtAreOne() {
        DecisionReading read = DecisionReadings.of("""
                module demo
                data Z = Int
                    invariant value >= 0
                behavior f : (a: Int, b: Int, z: Z) -> Int
                let f (a, b, z) = if a <= b then (if a <= b + z.value then 1 else 2) else 3
                """, "f");

        assertEquals(new DecisionReading.Enumeration.Complete(), read.enumeration());
        assertEquals(1, read.impossible().size(),
                () -> "z is never below nought, so a past b + z is past b: " + read.impossible());
    }

    @Test
    void theSameLinesWhereTheDifferenceCanFallBelowNoughtAreTwoBorders() {
        DecisionReading read = DecisionReadings.of("""
                module demo
                behavior f : (a: Int, b: Int, z: Int) -> Int
                let f (a, b, z) = if a <= b then (if a <= b + z then 1 else 2) else 3
                """, "f");

        assertEquals(new DecisionReading.Enumeration.Complete(), read.enumeration());
        assertEquals(List.of(), read.impossible(), "a negative z takes the way to 2");
        assertEquals(3, read.rules().size(), () -> "every way is a rule: " + read.rules());
    }

    @Test
    void aBodyWhoseInputHasNoValueIsNeverRead() {
        Compilation compilation = Compilation.ofSource("""
                module demo
                data Empty = Int
                    invariant value > 5 && value < 3
                behavior f : (e: Empty) -> Int
                let f (e) = if e.value > 4 then 1 else 2
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertFalse(compilation.diagnostics().values().stream().flatMap(List::stream)
                        .noneMatch(said -> said.diagnostic().severity() == Severity.ERROR),
                "a type with no value is refused");
        Map<String, ?> decides = compilation.db()
                .ask(new Adequacy.Decides(compilation.modules().getFirst())).value();
        assertNull(decides == null ? null : decides.get("f"),
                "so no reading of the body has every way dropped by a proof");
    }
}
