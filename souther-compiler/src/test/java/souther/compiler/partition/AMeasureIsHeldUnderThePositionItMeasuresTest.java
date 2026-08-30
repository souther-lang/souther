package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A measure measures something, and it is held under the location whose number it is of.
 *
 * <p>Two rules with one purpose. A location a behavior takes and a measure made of it are answers
 * to different questions — where a row is written, and what the rules divide — and a run of measures
 * that a location could stand in makes the second answer the first. That is what a measure with no
 * class, no line and nothing parted was: a location, counted among the measures and filtered back
 * out by every reader that could remember to.
 *
 * <p>So a measure of nothing cannot be built, and which location a measure is of is where it sits
 * rather than something a reader works out from how a path is spelled. What holds the two together
 * is checked once, where they are put together.
 */
class AMeasureIsHeldUnderThePositionItMeasuresTest {

    private static final String MODEL = """
            module example.held

            data Yes
            data No
            data Answer = Yes | No

            data Slot = { note: String, n: Int, m: Int }

            behavior gate : (slot: Slot) -> Answer
            let gate (slot) = {
                guard slot.n >= 5 else No
                guard slot.m >= 7 else No
                Yes
            }
            """;

    private static Partitions.Partitioning divided() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Partitions.Partitioning read = compilation.db()
                .ask(new Adequacy.Divided(compilation.modules().get(0), "gate")).value();
        assertNotNull(read, "the model under test compiles and is measured");
        return read;
    }

    private static PositionMeasurements at(String path) {
        PositionMeasurements found = divided().measurements().stream()
                .filter(each -> each.position().path().toString().equals(path))
                .findFirst().orElse(null);
        assertNotNull(found, "the behavior takes " + path);
        return found;
    }

    /** The state the run of measures could hold, refused where a measure is built. */
    @Test
    void aMeasureWithNoClassNoLineAndNoPartingCannotBeBuilt() {
        TermPath at = TermPath.of("slot").then("note");
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(at);

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new Axis(AxisId.of("gate", term), term, Type.STRING,
                        List.of(), List.of()));

        assertTrue(refused.getMessage().contains("measures a number of no")
                        || refused.getMessage().contains("at nothing"),
                refused.getMessage());
    }

    /**
     * And the model this compiler reads produces the location such a measure stood for, so the rule
     * above is about something. A plain string nothing compares is a position of the input and is
     * measured at no number.
     */
    @Test
    void aLocationNothingMeasuresIsAPositionWithNoMeasures() {
        PositionMeasurements note = at("slot.note");

        assertEquals(List.of(), note.axes());
        assertFalse(note.measured());
        assertTrue(divided().undivided().stream()
                        .anyMatch(each -> each.at().toString().equals("slot.note")),
                "and what a report says about it comes from the position");
    }

    /** While the location the rules do divide holds the measure they made of it. */
    @Test
    void aLocationTheRulesDivideHoldsTheMeasureOfIt() {
        PositionMeasurements n = at("slot.n");

        assertEquals(List.of("gate/slot.n"),
                n.axes().stream().map(each -> each.id().toString()).toList());
        assertTrue(n.measured());
    }

    /**
     * A measure of another location is not held here, and the two are never worked out apart.
     *
     * <p>Of a location holding the same type, so that the location is the only thing wrong with it:
     * a witness of another type would be refused for that whichever location it sat under.
     */
    @Test
    void aMeasureOfAnotherLocationIsNotHeldUnderThisOne() {
        PositionMeasurements n = at("slot.n");
        Axis ofAnother = at("slot.m").axes().get(0);
        assertEquals(n.position().type(), ofAnother.type(), "the two hold the same type");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new PositionMeasurements(n.position(), List.of(ofAnother), null));

        assertTrue(refused.getMessage().contains("slot.m")
                && refused.getMessage().contains("slot.n"), refused.getMessage());
    }

    /** Nor a measure that reads a value of another type, whatever it is called. */
    @Test
    void aMeasureThatReadsAnotherTypeIsNotHeldHere() {
        PositionMeasurements n = at("slot.n");
        Axis reading = n.axes().get(0);
        Axis ofAString = new Axis(reading.id(), reading.term(), Type.STRING,
                List.of(), reading.cuts());

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new PositionMeasurements(n.position(), List.of(ofAString), null));

        assertTrue(refused.getMessage().contains(Type.STRING.toString())
                && refused.getMessage().contains(Type.INT.toString()), refused.getMessage());
    }

    /** Nor one made for another behavior's input, which an axis names on its own. */
    @Test
    void aMeasureOfAnotherBehaviorsInputIsNotHeldHere() {
        PositionMeasurements n = at("slot.n");
        Axis reading = n.axes().get(0);
        Axis elsewhere = new Axis(AxisId.of("other", reading.term()), reading.term(),
                reading.type(), reading.classes(), reading.cuts());

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new PositionMeasurements(n.position(), List.of(elsewhere), null));

        assertTrue(refused.getMessage().contains("other"), refused.getMessage());
    }
}
