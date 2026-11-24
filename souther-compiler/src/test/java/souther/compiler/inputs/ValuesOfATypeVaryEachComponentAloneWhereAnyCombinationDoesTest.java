package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The values made of a record vary each component alone wherever some combination of the others
 * lets them, however far that combination is from the first values of the others.
 *
 * <p>What the values are asked for is that an order reading a record is held to each component, so a
 * component no two values differ in alone is one nothing asks about — and the maker refuses it
 * rather than passing over it. That refusal is a claim about the record, and is made only where
 * every combination of the others was asked: where the values nearest the first ones hold no such
 * pair, the asking goes on rather than stopping at the claim.
 *
 * <p>Each value of a component is put beside the nearest values of the others and no further, so a
 * value the constructor takes only beside more of them moved is not made; what that leaves out is
 * named by holding the nearest values against every combination, and the holding is asked here of a
 * record that leaves one out.
 */
class ValuesOfATypeVaryEachComponentAloneWhereAnyCombinationDoesTest {

    /**
     * Three flags a constructor ties together: two may differ only where the third is set, and all
     * three are not set at once.
     *
     * <p>Beside the first values — every flag clear — moving one other flag gives no value in which
     * the first or the second is set alone, and every pair varying either of them differs from the
     * first values in two flags: {@code 001} and {@code 101} vary the first, {@code 001} and
     * {@code 011} the second.
     */
    record Flags(boolean a, boolean b, boolean c) {

        Flags {
            if ((a != b && !c) || (a && b && c)) {
                throw new IllegalArgumentException("two flags differ only where the third is set");
            }
        }
    }

    @Test
    void aComponentVariedAloneOnlyFarFromTheFirstValuesIsVariedAlone() {
        List<Object> made = new ValuesOfAType().of(Flags.class);

        assertTrue(made.contains(new Flags(false, false, true))
                        && made.contains(new Flags(true, false, true)),
                () -> "the first flag varied alone: " + made);
        assertTrue(made.contains(new Flags(false, false, true))
                        && made.contains(new Flags(false, true, true)),
                () -> "the second flag varied alone: " + made);
    }

    /** A code of minus one, which the constructor takes only beside both flags set. */
    record Selective(int code, boolean b, boolean c) {

        Selective {
            if (code == -1 && (!b || !c)) {
                throw new IllegalArgumentException("minus one is a code only with both flags");
            }
        }
    }

    /**
     * A value a constructor ties to two other components is made, though the code is already
     * varied alone by nought and one: what is asked of each value is not answered by the asking of
     * each component.
     */
    @Test
    void aValueTiedToTwoOtherComponentsIsMade() {
        assertTrue(new ValuesOfAType().of(Selective.class).contains(new Selective(-1, true, true)));
    }

    /** A code of minus one, which the constructor takes only beside all three flags set. */
    record TiedToThree(int code, boolean b, boolean c, boolean d) {

        TiedToThree {
            if (code == -1 && (!b || !c || !d)) {
                throw new IllegalArgumentException("minus one is a code only with every flag");
            }
        }
    }

    /**
     * A value taken only beside three others moved is made over every combination and not beside
     * the nearest values, and holding the two against each other names it.
     */
    @Test
    void aValueTakenOnlyFarFromTheFirstValuesIsNamedWhereTheNearestLeaveItOut() {
        ValuesOfAType nearest = new ValuesOfAType();
        ValuesOfAType every = ValuesOfAType.everyCombination();
        nearest.of(TiedToThree.class);

        assertTrue(every.of(TiedToThree.class).contains(new TiedToThree(-1, true, true, true)),
                "every combination makes the code minus one");
        assertEquals(List.of(TiedToThree.class.getName() + ".code: [Optional[-1]]"),
                ValuesOfAType.valuesLeftOut(nearest, every));
    }

    /** Exactly one of two bounds is absent, so either partner of a counted word is accepted. */
    record OneBound(String counted, Long fewerThan, Long moreThan) {

        OneBound {
            if ((fewerThan == null) == (moreThan == null)) {
                throw new IllegalArgumentException("exactly one bound is absent");
            }
        }
    }

    /** What holds a list of them. */
    record HoldingBounds(List<OneBound> bounds) {}

    /**
     * Both ways of asking put a word beside the same partner, so a list of them is made of the same
     * records either way and nothing is named as left out.
     */
    @Test
    void aListOfRecordsWithTwoAcceptedPartnersIsMadeTheSameWayBothWays() {
        ValuesOfAType nearest = new ValuesOfAType();
        ValuesOfAType every = ValuesOfAType.everyCombination();

        assertEquals(nearest.of(HoldingBounds.class), every.of(HoldingBounds.class));
        assertEquals(List.of(), ValuesOfAType.valuesLeftOut(nearest, every));
    }

    /**
     * A code of minus one that is refused whatever stands beside it, among enough flags to count
     * through. Nought and one are taken, so the record is made whole when the search is let finish.
     */
    record RefusedEverywhere(boolean a, boolean b, boolean c, boolean d, int code) {

        RefusedEverywhere {
            if (code == -1) {
                throw new IllegalArgumentException("minus one is never a code");
            }
        }
    }

    /**
     * A search not finished within its budget is an error that says so, and one let finish gives
     * the absence it found. The error is told from the record's other refusal — a component varied
     * alone in no two values — by the message, and the control is the same record finishing with
     * room.
     */
    @Test
    void aSearchOverTooManyCombinationsIsAnErrorAndNotAnAbsence() {
        AssertionError error = assertThrows(AssertionError.class,
                () -> ValuesOfAType.everyCombination(3).of(RefusedEverywhere.class));
        assertTrue(error.getMessage().contains("was not finished after 3 constructions"),
                error.getMessage());
        assertTrue(error.getMessage().contains(RefusedEverywhere.class.getName()),
                error.getMessage());

        List<Object> made = ValuesOfAType.everyCombination().of(RefusedEverywhere.class);
        assertTrue(made.stream().noneMatch(each -> ((RefusedEverywhere) each).code() == -1),
                "minus one is not made");
        assertTrue(made.contains(new RefusedEverywhere(false, false, false, false, 1)),
                "the record is made whole");
    }

    /** The same tie, in a record over a type argument. */
    record GenericTiedToThree<T>(T code, boolean b, boolean c, boolean d) {

        GenericTiedToThree {
            if (Integer.valueOf(-1).equals(code) && (!b || !c || !d)) {
                throw new IllegalArgumentException("minus one is a code only with every flag");
            }
        }
    }

    /** What holds one, which is where it is made as the type it is over its argument. */
    record HoldingOne(GenericTiedToThree<Integer> held) {}

    /** And a generic record reached through another is held as the type it is made as. */
    @Test
    void aGenericRecordIsHeldAgainstEveryCombinationAsTheTypeItIsMadeAs() {
        ValuesOfAType nearest = new ValuesOfAType();
        ValuesOfAType every = ValuesOfAType.everyCombination();
        nearest.of(HoldingOne.class);
        every.of(HoldingOne.class);

        assertEquals(List.of(GenericTiedToThree.class.getName() + "<java.lang.Integer>.code:"
                        + " [Optional[-1]]"),
                ValuesOfAType.valuesLeftOut(nearest, every).stream()
                        .filter(each -> each.startsWith(GenericTiedToThree.class.getName()))
                        .toList());
    }
}
