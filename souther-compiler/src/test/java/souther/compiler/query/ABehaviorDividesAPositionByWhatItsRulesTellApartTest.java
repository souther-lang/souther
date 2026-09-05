package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Axis;
import souther.compiler.partition.PartitionClass;
import souther.compiler.partition.Partitions;
import souther.compiler.partition.Recognition;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior that treats some of the strings at a position differently divides that position.
 *
 * <p>The whole of what this issue is about, asked of the compiler rather than of any stage in it. An
 * invariant restricts a position — every value outside it is refused at construction — and a
 * behavior divides one: both sides of what a {@code guard} asks are values the model may hold, and a
 * run is on one side or the other. A position an author wrote such a rule for was coming back
 * undivided, so nothing owed a row on either side.
 *
 * <p>End to end because every stage between was already right about its own part. The rule was read,
 * what it admits was worked out, and the classes were built — from the tree where the operation had
 * been expanded into what it does, so there was no rule there to find. What this holds is the answer,
 * which is the only place all of it shows.
 */
class ABehaviorDividesAPositionByWhatItsRulesTellApartTest {

    @Test
    void aGuardOnWhatTheStringsAtAPositionAreDividesIt() {
        Axis axis = dividing("""
                behavior route : (code: String) -> Where
                let route (code) = {
                    guard String.startsWith("JP", code) else Abroad
                    Home
                }
                """);

        assertEquals(List.of(
                        "String.startsWith(\"JP\", x)",
                        "not String.startsWith(\"JP\", x)"),
                axis.classes().stream().map(PartitionClass::label).toList(),
                "the position is divided into what the rule admits and what it leaves");
    }

    /** And the classes are sets of the position's values, which is what such a rule states. */
    @Test
    void andEachClassIsTheValuesARunOfTheModelFallsIn() {
        Axis axis = dividing("""
                behavior route : (code: String) -> Where
                let route (code) = {
                    guard String.startsWith("JP", code) else Abroad
                    Home
                }
                """);

        for (PartitionClass each : axis.classes()) {
            Recognition.OfASet is = assertInstanceOf(Recognition.OfASet.class, each.recognises(),
                    "a class such a rule makes is the values in it");
            assertTrue(!is.values().isEmpty(), "and it holds some of them");
        }
    }

    /**
     * Two rules about one position leave it divided into what they come to between them.
     *
     * <p>Not two divisions of it. A run satisfies each or does not, so the rows are owed one class
     * at each of the four — taken a rule at a time, the denominator would be one partition of the
     * position stated twice.
     */
    @Test
    void twoRulesLeaveThePositionDividedIntoWhatTheyComeToBetweenThem() {
        Axis axis = dividing("""
                behavior route : (code: String) -> Where
                let route (code) = {
                    guard String.startsWith("JP", code) else Abroad
                    guard String.endsWith("-X", code) else Abroad
                    Home
                }
                """);

        assertEquals(4, axis.classes().size(),
                "the two rules come to four classes: " + axis.classes().stream()
                        .map(PartitionClass::label).toList());
    }

    /**
     * And a position both kinds of rule reach has no classes, rather than the ones the sets left.
     *
     * <p>A line on the order the values are counted on and a set of them are two vocabularies, and a
     * class in one cannot be written in the other. Divided by the half that happened to be
     * expressible, a run would be counted at a class the model tells apart from the one beside it.
     */
    @Test
    void aPositionBothKindsOfRuleReachHasNoClasses() {
        Axis axis = dividing("""
                behavior route : (code: String) -> Where
                let route (code) = {
                    guard String.startsWith("JP", code) else Abroad
                    guard code < "M" else Abroad
                    Home
                }
                """);

        assertEquals(List.of(), axis.classes().stream().map(PartitionClass::label).toList(),
                "the rules are not all sayable as one list of classes");
        // And what the ordering rule cut is untouched: the cuts are an observation of their own and
        // not a projection of the classes, so a border still knows where the values part.
        assertTrue(!axis.cuts().isEmpty(),
                "while where the rules cut the position is still what it was");
    }

    /** The one measure the model under test makes of its position. */
    private static Axis dividing(String behavior) {
        String source = """
                module demo

                data Home
                data Abroad
                data Where = Home | Abroad

                """ + behavior;
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        Partitions.Partitioning divided = compilation.db()
                .ask(new Adequacy.Divided(compilation.modules().get(0), "route")).value();
        assertNotNull(divided, "the behavior was divided");
        assertEquals(1, divided.axes().size(),
                "the model under test measures one number: " + divided.axes());
        return divided.axes().get(0);
    }
}
