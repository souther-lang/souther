package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A body that binds its input before comparing it divides the position the binding holds.
 *
 * <p>One rule written four ways. The value a {@code let} binds is evaluated on the way to the
 * answer, so a body that names its argument and then compares the name is comparing the argument —
 * which is what {@link souther.compiler.inputs.InputPath} says and what the measures have to read.
 *
 * <p>Written the other way round it is a hole under the spelling ADR-0054 prefers. That ADR lowers
 * the newtype pattern {@code X(v)} to the same {@code LetIn} + {@code FieldAccess(_, "value")}
 * chain a record destructuring lowers to, so a reading that stopped at the local would leave the
 * pattern form dividing no position while {@code .value} in the same body divided one — two
 * spellings of one model measured differently, and the one the ADR recommends is the silent one.
 *
 * <p>Measured against the spelling that reads through the field rather than against numbers written
 * down here. What the four have to agree on is the position and the lines, and an expectation
 * repeated four times would go on holding if every one of them fell silent together.
 */
class ABodyThatBindsItsInputBeforeComparingItComparesItsInputTest {

    private static final String MODEL = """
            module example.bound

            data Temp = Int

            data Cold
            data Comfortable
            data Hot

            behavior throughTheField : (temp: Temp) -> Cold | Comfortable | Hot
                constructs Cold, Comfortable, Hot
            let throughTheField (temp) =
                if temp.value < 240 then Cold
                else if temp.value < 260 then Comfortable
                else Hot
            example throughTheField
                | "cold"        : (Temp(200)) -> Cold
                | "comfortable" : (Temp(250)) -> Comfortable
                | "hot"         : (Temp(300)) -> Hot

            behavior openedInTheParameter : (temp: Temp) -> Cold | Comfortable | Hot
                constructs Cold, Comfortable, Hot
            let openedInTheParameter (Temp(t)) =
                if t < 240 then Cold
                else if t < 260 then Comfortable
                else Hot
            example openedInTheParameter
                | "cold"        : (Temp(200)) -> Cold
                | "comfortable" : (Temp(250)) -> Comfortable
                | "hot"         : (Temp(300)) -> Hot

            behavior openedInTheBody : (temp: Temp) -> Cold | Comfortable | Hot
                constructs Cold, Comfortable, Hot
            let openedInTheBody (temp) = {
                let Temp(t) = temp
                if t < 240 then Cold
                else if t < 260 then Comfortable
                else Hot
            }
            example openedInTheBody
                | "cold"        : (Temp(200)) -> Cold
                | "comfortable" : (Temp(250)) -> Comfortable
                | "hot"         : (Temp(300)) -> Hot

            behavior aliasedInTheBody : (temp: Temp) -> Cold | Comfortable | Hot
                constructs Cold, Comfortable, Hot
            let aliasedInTheBody (temp) = {
                let t = temp.value
                if t < 240 then Cold
                else if t < 260 then Comfortable
                else Hot
            }
            example aliasedInTheBody
                | "cold"        : (Temp(200)) -> Cold
                | "comfortable" : (Temp(250)) -> Comfortable
                | "hot"         : (Temp(300)) -> Hot
            """;

    /** The spellings that reach the parameter through a binding, each measured against the one that
     *  does not. */
    private static final List<String> BOUND =
            List.of("openedInTheParameter", "openedInTheBody", "aliasedInTheBody");

    private static Map<String, PartitionEvidence> measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
    }

    private static List<String> classesOf(PartitionEvidence evidence) {
        return evidence.axes().stream()
                .map(axis -> axis.path() + ": " + axis.classes())
                .toList();
    }

    private static List<String> linesOf(PartitionEvidence evidence) {
        return evidence.boundaries().stream()
                .map(line -> line.label() + " " + line.side())
                .sorted()
                .toList();
    }

    /** The reading everything else is held to: one position, cut where the body cuts it, with a row
     *  owed on each side of both lines. */
    @Test
    void theFieldSpellingDividesThePositionTheBodyCompares() {
        PartitionEvidence read = measured().get("throughTheField");

        assertEquals(List.of("temp: [temp/x < 240, temp/240 <= x < 260, temp/260 <= x]"),
                classesOf(read));
        assertEquals(List.of("temp = 239 BELOW", "temp = 240 AT",
                        "temp = 259 BELOW", "temp = 260 AT"),
                linesOf(read));
    }

    /** And every spelling that binds the input first divides it the same way. */
    @Test
    void aBoundSpellingDividesWhatTheFieldSpellingDivides() {
        Map<String, PartitionEvidence> measured = measured();
        PartitionEvidence held = measured.get("throughTheField");

        for (String behavior : BOUND) {
            assertEquals(classesOf(held), classesOf(measured.get(behavior)), behavior);
            assertEquals(linesOf(held), linesOf(measured.get(behavior)), behavior);
        }
    }

    /** None of them leaves its input among the positions no class came back for. A body whose input
     *  is bound first used to be reported there — either as a position nothing could be derived at
     *  or as one the model divides no way, and both are the opposite of what the two lines under it
     *  say. */
    @Test
    void noSpellingNamesItsInputAsAPositionNothingDivides() {
        Map<String, PartitionEvidence> measured = measured();
        for (String behavior : BOUND) {
            assertEquals(List.of(), measured.get(behavior).notDerivable(), behavior);
            assertEquals(List.of(), measured.get(behavior).notRead(), behavior);
        }
    }
}
