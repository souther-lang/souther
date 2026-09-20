package souther.compiler.observe;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.TermPath;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** What {@link ElementsTaken} keeps of the steps a value was reached through, and what it says of
 *  two values that share some of them. */
class ElementsTakenAreHeldOutermostFirstTest {

    private static final TermPath PEOPLE = TermPath.of("row").then("people").element();
    private static final TermPath PHONES = PEOPLE.then("phones").element();
    private static final TermPath ADDRESSES = PEOPLE.then("addresses").element();

    @Test
    void theStepsAreKeptInTheOrderTheyWereTaken() {
        ElementsTaken inside = ElementsTaken.NONE.and(PEOPLE, 1).and(PHONES, 0);

        assertEquals(List.of(new ElementsTaken.Taken(PEOPLE, 1), new ElementsTaken.Taken(PHONES, 0)),
                inside.outermostFirst(),
                "the sequence a reader builds readings over is walked from the outermost step in");
    }

    @Test
    void whatWasTakenAtAStepIsAskedByTheStep() {
        ElementsTaken inside = ElementsTaken.NONE.and(PEOPLE, 1).and(PHONES, 0);

        assertEquals(1, inside.elementAt(PEOPLE));
        assertEquals(0, inside.elementAt(PHONES));
        assertNull(inside.elementAt(ADDRESSES), "a step this took no part in has no element");
    }

    @Test
    void twoValuesAgreeWhereEveryStepTheyShareWasTakenAtOneElement() {
        ElementsTaken first = ElementsTaken.NONE.and(PEOPLE, 1).and(PHONES, 0);
        ElementsTaken sameAddress = ElementsTaken.NONE.and(PEOPLE, 1).and(ADDRESSES, 2);
        ElementsTaken anotherPerson = ElementsTaken.NONE.and(PEOPLE, 0).and(ADDRESSES, 2);

        assertTrue(first.agreesWith(sameAddress),
                "one person, and the phone and the address are each free of the other");
        assertFalse(first.agreesWith(anotherPerson), "another person is another reading");
        assertEquals(first.agreesWith(anotherPerson), anotherPerson.agreesWith(first));
    }

    @Test
    void aStepIsTakenOnceAndAtAStep() {
        ElementsTaken inside = ElementsTaken.NONE.and(PEOPLE, 1);

        assertThrows(IllegalArgumentException.class, () -> inside.and(PEOPLE, 0),
                "two elements at one step are two readings in one value, and agreement between"
                        + " values would depend on which side was asked");
        assertThrows(NullPointerException.class, () -> new ElementsTaken.Taken(null, 0));
    }

    @Test
    void agreementIsTheSameFromEitherSide() {
        List<ElementsTaken> values = List.of(ElementsTaken.NONE,
                ElementsTaken.NONE.and(PEOPLE, 0), ElementsTaken.NONE.and(PEOPLE, 1),
                ElementsTaken.NONE.and(PEOPLE, 1).and(PHONES, 0),
                ElementsTaken.NONE.and(PEOPLE, 1).and(PHONES, 1),
                ElementsTaken.NONE.and(PEOPLE, 0).and(ADDRESSES, 2));

        for (ElementsTaken one : values) {
            for (ElementsTaken other : values) {
                assertEquals(one.agreesWith(other), other.agreesWith(one), one + " and " + other);
            }
        }
    }

    @Test
    void aValueInsideNoSequenceStandsWithEveryOther() {
        ElementsTaken inside = ElementsTaken.NONE.and(PEOPLE, 1);

        assertTrue(ElementsTaken.NONE.agreesWith(inside));
        assertTrue(inside.agreesWith(ElementsTaken.NONE));
    }
}
