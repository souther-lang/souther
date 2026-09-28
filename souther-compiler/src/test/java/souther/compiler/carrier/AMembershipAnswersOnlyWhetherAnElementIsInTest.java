package souther.compiler.carrier;

import org.junit.jupiter.api.Test;

import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** What a {@link Membership} answers, and what it refuses to become once it is built. */
class AMembershipAnswersOnlyWhetherAnElementIsInTest {

    @Test
    void twoMembershipsFilledInDifferentOrdersAreOneValue() {
        Membership<String> first = Membership.built(add -> {
            add.add("a");
            add.add("b");
        });
        Membership<String> second = Membership.built(add -> {
            add.add("b");
            add.add("a");
        });

        assertEquals(first, second, "what is in is the same value, whichever order the two were"
                + " filled in");
        assertEquals(first.hashCode(), second.hashCode());
    }

    @Test
    void anElementIsInOnlyIfItWasStated() {
        Membership<String> membership = Membership.built(add -> add.add("a"));

        assertTrue(membership.contains("a"));
        assertFalse(membership.contains("b"));
    }

    @Test
    void anElementStatedTwiceIsWhatStatingItOnceSaid() {
        Membership<String> once = Membership.built(add -> add.add("a"));
        Membership<String> twice = Membership.built(add -> {
            add.add("a");
            add.add("a");
        });

        assertEquals(once, twice, "stating an element again says nothing stating it did not");
    }

    @Test
    void anElementOfNullIsRefusedWhetherItIsStatedOrAskedAbout() {
        assertThrows(NullPointerException.class,
                () -> Membership.<String>built(add -> add.add(null)));
        assertThrows(NullPointerException.class,
                () -> Membership.<String>built(add -> add.add("a")).contains(null));
    }

    @Test
    void aCallerThatKeepsTheMembersCannotChangeWhatWasAlreadyBuilt() {
        AtomicReference<Membership.Members<String>> kept = new AtomicReference<>();

        Membership<String> built = Membership.built(add -> {
            add.add("a");
            kept.set(add);
        });

        kept.get().add("b");

        assertFalse(built.contains("b"), "built was handed a snapshot once the callback that filled"
                + " it returned, so stating an element through a kept Members afterward cannot"
                + " change what built holds");
    }

    // Nothing tests that a Membership is not a Set, a Collection or an Iterable: Membership is a
    // final class implementing none of them, so `instanceof` against any of those is a compile
    // error rather than a runtime question.
}
