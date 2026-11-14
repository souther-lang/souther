package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementBindings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading watched for what it asked of the values an application handed is told from another by
 * those answers alone only if every read it made was placed.
 *
 * <p>A read is made in the environment the watch began on, in one made from it, or in one that is
 * neither. The first two are placed: the reading asked after what the environment began with, or it
 * handed the name a value itself since. The third cannot be: what it was answered is no answer of
 * the environment another reading is compared with, so a watch that went on without it would say
 * the reading depended on nothing it could not place, and a reading with different values behind
 * that read would be taken for the same one.
 */
class AWatchedReadingAsksOnlyWhatItCanPlaceOfWhatWasHandedTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");
    private static final BindingId EACH = new BindingId(OWNER, 0);
    private static final BindingId OTHER = new BindingId(OWNER, 1);

    private static BindingEnvironment nothingHanded() {
        return new BindingEnvironment(Map.of(), Map.of(), ElementBindings.NONE,
                ValueDefinitions.NONE, false);
    }

    private static Core written(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    /** Reads what {@code binding} is handed in {@code reading}, while a watch began on
     *  {@code on}. */
    private static HandedAnswers asked(BindingEnvironment on, BindingEnvironment reading,
                                       BindingId binding) {
        return BindingEnvironment.Watch.over(on, () -> reading.roleOf(binding)).asked();
    }

    @Test
    void aReadInTheEnvironmentTheWatchBeganOnIsPlacedAndAnsweredAsItWas() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));

        HandedAnswers asked = asked(on, on, EACH);

        assertTrue(asked.toldApart());
        assertTrue(asked.holdsOf(on));
        assertFalse(asked.holdsOf(nothingHanded().handing(EACH, written(2))),
                "the reading asked after EACH, and was answered 1");
        assertTrue(asked.holdsOf(nothingHanded().handing(EACH, written(1))
                .handing(OTHER, written(9))), "and asked nothing of what else is handed");
    }

    @Test
    void aReadInAnEnvironmentMadeFromItIsPlacedWhereTheNameIsNotHandedAgain() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment since = on.handing(OTHER, written(5));

        HandedAnswers asked = asked(on, since, EACH);

        assertTrue(asked.toldApart());
        assertFalse(asked.holdsOf(nothingHanded().handing(EACH, written(2))),
                "EACH was handed on the way to the reading before the reading began");
        assertTrue(asked.holdsOf(on));
    }

    @Test
    void aNameHandedAValueSinceIsTheReadingsOwnAndAsksNothingOfWhatWasHandedBefore() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment since = on.handing(EACH, written(7));

        HandedAnswers asked = asked(on, since, EACH);

        assertTrue(asked.toldApart());
        assertTrue(asked.holdsOf(nothingHanded().handing(EACH, written(2))),
                "what EACH was handed before the reading is no answer it was given");
    }

    @Test
    void aReadInAnEnvironmentApartFromTheOneTheWatchBeganOnIsNotPlaced() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment apart = nothingHanded().handing(EACH, written(1));

        HandedAnswers asked = asked(on, apart, EACH);

        assertFalse(asked.toldApart(), "equal to the one it began on, and not the one");
        assertSame(HandedAnswers.UNTOLD, asked);
        assertFalse(asked.holdsOf(on));
    }

    @Test
    void aReadInAnAncestorOfTheEnvironmentTheWatchBeganOnIsNotPlaced() {
        BindingEnvironment before = nothingHanded().handing(EACH, written(1));
        BindingEnvironment on = before.handing(OTHER, written(2));

        HandedAnswers asked = asked(on, before, EACH);

        assertFalse(asked.toldApart(),
                "what it was answered is an answer of an environment before this one");
        assertFalse(asked.holdsOf(on));
    }

    @Test
    void aReadingThatReadsNothingHandedIsToldApartByNoAnswerAndHoldsOfEveryEnvironment() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));

        HandedAnswers asked = BindingEnvironment.Watch.over(on, () -> 0).asked();

        assertTrue(asked.toldApart());
        assertTrue(asked.holdsOf(nothingHanded()));
        assertTrue(asked.holdsOf(on));
    }

    @Test
    void aReadingInsideAnotherWatchIsWatchedOnItsOwnAndTheOuterOneAsksWhatItAsked() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment otherwise = nothingHanded().handing(EACH, written(2));

        Watched<HandedAnswers> outer = BindingEnvironment.Watch.over(on, () ->
                BindingEnvironment.Watch.over(on, () -> on.roleOf(EACH)).asked());

        assertTrue(outer.result().toldApart());
        assertTrue(outer.result().holdsOf(on));
        assertFalse(outer.result().holdsOf(otherwise));
        assertTrue(outer.asked().toldApart());
        assertTrue(outer.asked().holdsOf(on));
        assertFalse(outer.asked().holdsOf(otherwise),
                "what the inner reading asked of EACH is asked of the outer one as well");
    }

    @Test
    void aReadingTakenAgainInsideAWatchTellsItWhatItAsked() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment otherwise = nothingHanded().handing(EACH, written(2));
        HandedAnswers asked = BindingEnvironment.Watch.over(on, () -> on.roleOf(EACH)).asked();

        HandedAnswers outer = BindingEnvironment.Watch.over(on, () -> {
            BindingEnvironment.Watch.replay(on, asked);
            return 0;
        }).asked();

        assertTrue(outer.toldApart());
        assertTrue(outer.holdsOf(on));
        assertFalse(outer.holdsOf(otherwise));
    }

    @Test
    void anUnplacedReadInsideAnotherWatchLeavesTheOuterOneUnsureToo() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment apart = nothingHanded().handing(OTHER, written(1));

        Watched<HandedAnswers> outer = BindingEnvironment.Watch.over(on, () ->
                BindingEnvironment.Watch.over(on, () -> apart.roleOf(OTHER)).asked());

        assertFalse(outer.result().toldApart());
        assertFalse(outer.asked().toldApart());
    }

    @Test
    void anUnplacedReadAfterAPlacedOneStillLeavesTheWatchUnsure() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment apart = nothingHanded().handing(OTHER, written(1));

        HandedAnswers asked = BindingEnvironment.Watch.over(on, () -> {
            BindingRole placed = on.roleOf(EACH);
            return List.of(placed, apart.roleOf(OTHER));
        }).asked();

        assertFalse(asked.toldApart());
    }

    private static final BindingId THIRD = new BindingId(OWNER, 2);

    @Test
    void aNameHandedAgainTheSameValueSinceIsStillTheReadingsOwn() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment since = on.handing(EACH, written(1));

        HandedAnswers asked = BindingEnvironment.Watch.over(on, () ->
                BindingEnvironment.Watch.over(on, () -> since.roleOf(EACH)).asked()).asked();

        assertTrue(asked.toldApart());
        assertTrue(asked.holdsOf(nothingHanded().handing(EACH, written(2))),
                "equal to what the watch began with, and handed since all the same");
    }

    @Test
    void aSetTakenInAcrossSeveralStepsLeavesOutTheNamesHandedOnAnyOfThem() {
        BindingEnvironment on = nothingHanded();
        BindingEnvironment far = on.handing(EACH, written(1)).handing(OTHER, written(2))
                .handing(EACH, written(3));

        HandedAnswers asked = BindingEnvironment.Watch.over(on, () ->
                BindingEnvironment.Watch.over(on, () -> {
                    far.roleOf(EACH);
                    far.roleOf(OTHER);
                    return far.roleOf(THIRD);
                }).asked()).asked();

        assertTrue(asked.toldApart());
        assertTrue(asked.holdsOf(nothingHanded().handing(EACH, written(9))
                .handing(OTHER, written(9))), "EACH and OTHER were handed on the way");
        assertFalse(asked.holdsOf(nothingHanded().handing(THIRD, written(9))),
                "THIRD was not, and the watch began with it handed nothing");
    }

    @Test
    void aReadingTakenAgainFromAnEnvironmentSinceLeavesOutWhatWasHandedOnTheWay() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment since = on.handing(OTHER, written(5));
        HandedAnswers asked = BindingEnvironment.Watch.over(since, () -> {
            since.roleOf(EACH);
            return since.roleOf(OTHER);
        }).asked();

        HandedAnswers outer = BindingEnvironment.Watch.over(on, () -> {
            BindingEnvironment.Watch.replay(since, asked);
            return 0;
        }).asked();

        assertTrue(outer.toldApart());
        assertFalse(outer.holdsOf(nothingHanded().handing(EACH, written(2))));
        assertTrue(outer.holdsOf(nothingHanded().handing(EACH, written(1))
                .handing(OTHER, written(8))), "OTHER was handed since the watch began");
    }

    @Test
    void aSetOfNoNameTakenInFromAnEnvironmentApartLeavesTheWatchSure() {
        BindingEnvironment on = nothingHanded().handing(EACH, written(1));
        BindingEnvironment apart = nothingHanded().handing(OTHER, written(1));
        HandedAnswers nothing = BindingEnvironment.Watch.over(apart, () -> 0).asked();

        HandedAnswers outer = BindingEnvironment.Watch.over(on, () -> {
            BindingEnvironment.Watch.replay(apart, nothing);
            return 0;
        }).asked();

        assertTrue(outer.toldApart());
    }

    @Test
    void aSetOfNamesAllHandedAgainSinceTakenInFromAnEnvironmentApartIsStillUnplaced() {
        BindingEnvironment on = nothingHanded().handing(OTHER, written(1));
        BindingEnvironment apart = nothingHanded().handing(EACH, written(1));
        HandedAnswers asked = BindingEnvironment.Watch.over(apart, () -> apart.roleOf(EACH))
                .asked();

        HandedAnswers outer = BindingEnvironment.Watch.over(on, () -> {
            BindingEnvironment.Watch.replay(apart, asked);
            return 0;
        }).asked();

        assertFalse(outer.toldApart());
    }

    @Test
    void aNameHandedNothingIsAnAnswerAndAHandedValueBreaksIt() {
        BindingEnvironment on = nothingHanded();

        HandedAnswers asked = BindingEnvironment.Watch.over(on, () -> on.roleOf(EACH)).asked();

        assertTrue(asked.holdsOf(nothingHanded().handing(OTHER, written(1))));
        assertFalse(asked.holdsOf(nothingHanded().handing(EACH, written(1))),
                "asked after, and was handed nothing");
    }
}
