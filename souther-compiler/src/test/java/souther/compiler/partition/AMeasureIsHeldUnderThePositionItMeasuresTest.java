package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
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

    /** What the rules came to where every one of them was read and none drew a line, which is what
     *  the fixtures below are not about. */
    private static final BodyCutInspection READ_TO_THE_END = new BodyCutInspection.Exhausted();

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
                () -> new Axis(AxisId.of("gate", term), term, List.of(), List.of()));

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
        assertFalse(note.hasMeasures());
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
        assertTrue(n.hasMeasures());
    }

    /**
     * Three questions about one location, and no two of them are the same question.
     *
     * <p>Whether anything measures it, whether a measure of it asks a row for anything, and which
     * of its measures divide their number into classes. A measure that parts a number where the
     * location holds no value answers the first and neither of the others, which is the one value
     * that tells the three apart — and every one of them has a reader that the other two would
     * answer wrongly. The location is measured, so nothing is pending at it and a report says
     * nothing about it being undivided; there is nothing at the parting to ask an author for, so no
     * line is assembled along it; and it divides the number into no classes, so no partition counts
     * it.
     */
    @Test
    void aMeasureThatOnlyPartsANumberIsAMeasureAndAsksForNoRow() {
        PositionMeasurements n = at("slot.n");
        Axis reading = n.axes().get(0);
        Carrier whole = new Carrier.Whole();
        Axis partsOnly = new Axis(reading.id(), reading.term(), List.of(),
                List.of(),
                List.of(Parting.by(
                        Seam.of(LevelSpace.onACarrier(whole),
                                new Level.OnACarrier(whole, Count.of(java.math.BigDecimal.TEN)),
                                Towards.BELOW),
                        WhatTheRulesTogetherLeaveAQuantityTest.aLine(1))),
                souther.compiler.check.NarrowedBounds.NOTHING);
        PositionMeasurements parting =
                new PositionMeasurements(n.position(), List.of(partsOnly), READ_TO_THE_END);

        assertTrue(parting.hasMeasures(), "the rules part the number, which is a measure of it");
        assertFalse(partsOnly.asksForARow(),
                "and the location holds no value at the parting, so nothing is owed a row");
        assertEquals(List.of(), parting.partitionAxes(),
                "and it divides the number into no classes");
        assertNull(PendingPosition.of(parting.position(), parting.hasMeasures()),
                "so the location is answered for, and a report says nothing about it being"
                        + " undivided");
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
        assertEquals(n.position().type(), at("slot.m").position().type(),
                "the two locations hold the same type, so what refuses this is the path");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new PositionMeasurements(n.position(), List.of(ofAnother), READ_TO_THE_END));

        assertTrue(refused.getMessage().contains("slot.m")
                && refused.getMessage().contains("slot.n"), refused.getMessage());
    }

    /**
     * A measure is named after the number it is of, so its name cannot say another.
     *
     * <p>The name is what every reader downstream holds a measure under — the lines along it, what
     * a row was placed at, what a piece of evidence was measured by — so a measure of one number
     * filed under the name of another is not a wrong word in a report; it is that reader holding
     * the wrong measure.
     */
    @Test
    void aMeasureCannotBeNamedAfterANumberItDoesNotMeasure() {
        Axis reading = at("slot.n").axes().get(0);

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new Axis(AxisId.of("gate", at("slot.m").axes().get(0).term()),
                        reading.term(), reading.classes(), reading.cuts()));

        assertTrue(refused.getMessage().contains("slot.m")
                && refused.getMessage().contains("slot.n"), refused.getMessage());
    }

    /** And a location is measured once at each number, because that name is what tells them apart. */
    @Test
    void aLocationIsNotMeasuredTwiceAtOneNumber() {
        PositionMeasurements n = at("slot.n");
        Axis once = n.axes().get(0);

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new PositionMeasurements(n.position(), List.of(once, once), READ_TO_THE_END));

        assertTrue(refused.getMessage().contains("twice"), refused.getMessage());
    }

    /** And what the rules about the location came to is part of the answer, not something a reader
     *  waits for. */
    @Test
    void aLocationAnsweredForSaysWhatItsRulesCameTo() {
        PositionMeasurements n = at("slot.n");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new PositionMeasurements(n.position(), n.axes(), null));

        assertTrue(refused.getMessage().contains("slot.n"), refused.getMessage());
    }

    /** Nor one made for another behavior's input, which an axis names on its own. */
    @Test
    void aMeasureOfAnotherBehaviorsInputIsNotHeldHere() {
        PositionMeasurements n = at("slot.n");
        Axis reading = n.axes().get(0);
        Axis elsewhere = new Axis(AxisId.of("other", reading.term()), reading.term(),
                reading.classes(), reading.cuts());

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new PositionMeasurements(n.position(), List.of(elsewhere), READ_TO_THE_END));

        assertTrue(refused.getMessage().contains("other"), refused.getMessage());
    }
}
