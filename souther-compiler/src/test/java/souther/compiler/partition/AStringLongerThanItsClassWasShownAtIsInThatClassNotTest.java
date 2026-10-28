package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import souther.compiler.inputs.Membership;
import souther.compiler.observe.ObservedValue;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.ValueSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A class shown only as far as some length holds a string of its set up to that length, and a
 * longer one is in it not: such a string was shown on neither side of the rule that drew the class,
 * so a row writing it is counted at no class of the position.
 */
class AStringLongerThanItsClassWasShownAtIsInThatClassNotTest {

    private static ValueSet matching(String regex) {
        PatternRead said = PatternParser.read(regex);
        return ValueSet.matching(PatternPlan.of(
                        assertInstanceOf(PatternRead.Read.class, said, regex).meaning())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()));
    }

    @Test
    void aStringUpToTheLengthIsInTheClassAndALongerOneIsNot() {
        Recognition upToThree = new Recognition.OfASet(matching("[a-z]+"), 3L);

        assertEquals(Membership.MATCH,
                Recognitions.membershipOf(upToThree, new ObservedValue.Text("abc")));
        assertEquals(Membership.NO_MATCH,
                Recognitions.membershipOf(upToThree, new ObservedValue.Text("abcd")));
    }

    /** Counted in code points, as a string's length is. */
    @Test
    void theLengthIsCountedInCodePoints() {
        Recognition upToTwo = new Recognition.OfASet(matching(".+"), 2L);

        assertEquals(Membership.MATCH,
                Recognitions.membershipOf(upToTwo, new ObservedValue.Text("😀a")));
    }

    /** A class shown at every length holds every string of its set. */
    @Test
    void aClassShownAtEveryLengthHoldsEveryStringOfItsSet() {
        assertEquals(Membership.MATCH, Recognitions.membershipOf(
                new Recognition.OfASet(matching("[a-z]+"), null),
                new ObservedValue.Text("abcdefgh")));
    }
}
