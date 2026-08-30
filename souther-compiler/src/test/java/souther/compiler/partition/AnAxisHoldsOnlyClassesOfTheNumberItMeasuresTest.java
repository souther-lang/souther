package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An axis is a run of classes over one number, and the classes it holds are classes of that number.
 *
 * <p>Two things a class can be of, and only one of them can be asked with a place on the number's
 * order: a class about a count says which number it counts, and every other class is about the value
 * standing at the position. A class of the second kind on an axis measuring something taken of the
 * position leaves the two with nothing to compare — a class of times has no answer about which run a
 * minute falls in — and asking anyway comes back as the class not being found, which reads as the
 * rules dividing the position nowhere.
 *
 * <p>Built by hand here rather than searched for in a model. No model this compiler reads today
 * produces such an axis, which is the reason to hold the rule at the way in rather than to rely on
 * the corpus: what is being fixed is that the axis cannot be built, and a fixture that has to be
 * found first would be a test of which models exist.
 */
class AnAxisHoldsOnlyClassesOfTheNumberItMeasuresTest {

    private static final String MODEL = """
            module example.subject

            data Yes
            data No
            data Answer = Yes | No

            data Slot =
                { c: String
                , n: Int
                , on: Bool
                }

            behavior gate : (slot: Slot) -> Answer
            let gate (slot) = {
                guard String.length(slot.c) >= 3 else No
                guard slot.n >= 5 else No
                Yes
            }
            """;

    /** What the model divides, which is where the classes below come from. */
    private static Partitions.Partitioning divided() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db()
                .ask(new Adequacy.Divided(compilation.modules().get(0), "gate")).value();
    }

    private static Axis axisOf(Partitions.Partitioning read, String id) {
        Axis found = read.axes().stream().filter(each -> each.id().toString().equals(id))
                .findFirst().orElse(null);
        assertNotNull(found, "the model is measured at " + id + ", among " + read.axes().stream()
                .map(each -> each.id().toString()).toList());
        return found;
    }

    /**
     * The classes each axis has are of its own number, which is what the rest of this is about.
     *
     * <p>Asserted so that the refusals below are about a rule that lets the model through. A check
     * that refused every class would pass them and leave nothing measured.
     */
    @Test
    void aModelsOwnAxesHoldTheirOwnClasses() {
        Partitions.Partitioning read = divided();

        Axis length = axisOf(read, "gate/String.length(slot.c)");
        Axis count = axisOf(read, "gate/slot.n");
        Axis truth = axisOf(read, "gate/slot.on");

        assertEquals(List.of(length.term()), length.classes().stream()
                .map(PartitionClass::of).distinct().toList(),
                "every class of the length is a class of the length");
        assertEquals(List.of(count.term()), count.classes().stream()
                .map(PartitionClass::of).distinct().toList());
        assertEquals(List.of(truth.term()), truth.classes().stream()
                .map(PartitionClass::of).distinct().toList(),
                "and a truth is a class of the value standing at the position it was read for");
        assertFalse(truth.classes().isEmpty(), "of which this model has some");
    }

    /**
     * A class of one position's value is not a class of another's.
     *
     * <p>The two are told apart by the measure they were built for and never by what they mean: a
     * truth means the same thing at every position, and a rule reading which number a class is of
     * out of its meaning has nothing to read here — so both positions' classes would answer alike
     * and either would pass for the other.
     */
    @Test
    void aClassOfAnotherPositionsValueIsRefused() {
        Partitions.Partitioning read = divided();
        Axis count = axisOf(read, "gate/slot.n");
        Axis truth = axisOf(read, "gate/slot.on");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> count.carrying(truth.classes(), List.of(), List.of()));

        assertTrue(refused.getMessage().contains("slot.on")
                        && refused.getMessage().contains("slot.n"),
                refused.getMessage());
    }

    /** And a class built for no measure at all is not one either, whichever axis is offered it. */
    @Test
    void aClassBuiltForNoMeasureIsRefused() {
        Partitions.Partitioning read = divided();
        Axis count = axisOf(read, "gate/slot.n");
        List<PartitionClass> unstamped = count.classes().stream()
                .map(each -> PartitionClass.of(each.id(), each.label(), each.recognises(),
                        each.representatives()))
                .toList();

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> count.carrying(unstamped, List.of(), List.of()));

        assertTrue(refused.getMessage().contains("no measure"), refused.getMessage());
    }

    /** A class of one number is not a class of another, whichever position both are read from. */
    @Test
    void aClassOfAnotherNumberIsRefused() {
        Partitions.Partitioning read = divided();
        Axis length = axisOf(read, "gate/String.length(slot.c)");
        Axis count = axisOf(read, "gate/slot.n");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> length.carrying(count.classes(), List.of(), List.of()));

        assertTrue(refused.getMessage().contains("slot.n")
                        && refused.getMessage().contains("String.length(slot.c)"),
                refused.getMessage());
    }

    /**
     * A class about the value standing at a position is not a class of a number taken of it.
     *
     * <p>The mixed axis a reading would produce by keeping what the declarations divide a position
     * into while measuring the position at something taken of it.
     */
    @Test
    void aClassOfTheValueAtThePositionIsRefusedWhereTheNumberIsTakenOfIt() {
        Partitions.Partitioning read = divided();
        Axis length = axisOf(read, "gate/String.length(slot.c)");
        Axis truth = axisOf(read, "gate/slot.on");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> length.carrying(truth.classes(), List.of(), List.of()));

        assertTrue(refused.getMessage().contains("String.length(slot.c)"), refused.getMessage());
    }

    /**
     * And is one of the axis measuring the value itself, where what stands at the position is the
     * number.
     */
    @Test
    void aClassOfTheValueAtThePositionIsKeptWhereTheAxisMeasuresThatValue() {
        Partitions.Partitioning read = divided();
        Axis truth = axisOf(read, "gate/slot.on");

        Axis again = truth.carrying(truth.classes(), List.of(), List.of());

        assertEquals(truth.classes(), again.classes());
    }

    /**
     * The same position measured at another number keeps the position and none of the old number's
     * answers.
     *
     * <p>What the classes and the lines are is how the rules divided one number and where they cut
     * it, so the position measured at a second number starts with none of them and is given what the
     * rules leave that number. Carried over, they would be the classes of one number on an axis of
     * another, which is the thing above that cannot be built.
     */
    @Test
    void thePositionMeasuredAtAnotherNumberCarriesNoneOfTheFirstsClasses() {
        Partitions.Partitioning read = divided();
        Axis length = axisOf(read, "gate/String.length(slot.c)");
        Axis count = axisOf(read, "gate/slot.n");
        assertFalse(length.classes().isEmpty(), "there is something to be carried or dropped");

        Axis elsewhere = length.measuredAt(count.id(), count.term());

        assertEquals(List.of(), elsewhere.classes());
        assertEquals(List.of(), elsewhere.cuts());
        assertSame(length.at(), elsewhere.at(), "and the position is the position");
    }

    /**
     * Two namings of one number are one subject, which is what the rule compares with.
     *
     * <p>A term built here and the one the reading built are different objects and the same number,
     * and the classes of that number belong to an axis measuring it however it was arrived at. Held
     * by identity rather than by what a term is, the rule would refuse them and would do so
     * depending on where the axis had been built.
     */
    @Test
    void aClassIsOfTheNumberAndNotOfTheObjectThatNamesIt() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Partitions.Partitioning read = compilation.db()
                .ask(new Adequacy.Divided(module, "gate")).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Axis length = axisOf(read, "gate/String.length(slot.c)");

        TermPath at = TermPath.of("slot").then("c");
        NumericTerm.TakenOf again = NumericTerm.TakenOf.of(
                NumericMeasures.takenOf(Type.STRING, symbols), at, Type.STRING, symbols);

        assertNotNull(again, "the length of a string is a number this compiler names");
        assertNotSame(length.term(), again, "a second naming, built here");
        assertEquals(length.term(), again, "of the number the reading already named");
        assertSame(again, length.measuredAt(length.id(), again).term(),
                "so the classes of that number are the classes of an axis measuring it");
        assertEquals(length.classes(),
                length.measuredAt(length.id(), again).classes());
    }
}
