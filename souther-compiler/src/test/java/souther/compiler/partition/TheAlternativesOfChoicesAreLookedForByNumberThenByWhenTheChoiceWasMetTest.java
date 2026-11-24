package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The order alternatives are looked for ways in ({@link AlternativeOrder}): the smaller number
 * first, and among those of one number the choice met first — the choices met while it is being
 * walked included, which join the order at their place and not after it.
 */
class TheAlternativesOfChoicesAreLookedForByNumberThenByWhenTheChoiceWasMetTest {

    private static List<String> drained(AlternativeOrder<String> order) {
        List<String> out = new ArrayList<>();
        for (AlternativeOrder.Target<String> each = order.next(); each != null;
                each = order.next()) {
            out.add(each.choice() + each.alternative());
        }
        return out;
    }

    @Test
    void theSmallerNumberComesFirstAndAmongTheSameNumberTheChoiceMetFirst() {
        AlternativeOrder<String> order = new AlternativeOrder<>();
        order.met("a", 3);
        order.met("b", 2);

        assertEquals(List.of("a0", "b0", "a1", "b1", "a2"), drained(order));
    }

    @Test
    void aChoiceMetLaterIsOwedItsSmallerNumbersBeforeTheLargerOnesAlreadyMet() {
        AlternativeOrder<String> order = new AlternativeOrder<>();
        order.met("a", 4);
        List<String> out = new ArrayList<>();
        // The first three are asked, and the choice an alternative holds is met on the way.
        for (int each = 0; each < 3; each++) {
            AlternativeOrder.Target<String> target = order.next();
            out.add(target.choice() + target.alternative());
        }
        order.met("inner", 2);
        out.addAll(drained(order));

        assertEquals(List.of("a0", "a1", "a2", "inner0", "inner1", "a3"), out);
    }

    @Test
    void twoChoicesThatAreEqualAreTwoChoices() {
        AlternativeOrder<String> order = new AlternativeOrder<>();
        order.met("same", 2);
        order.met("same", 2);

        assertEquals(List.of("same0", "same0", "same1", "same1"), drained(order));
    }

    @Test
    void nothingIsOwedOfAChoiceWithNoAlternative() {
        AlternativeOrder<String> order = new AlternativeOrder<>();
        order.met("none", 0);

        assertNull(order.next());
    }
}
