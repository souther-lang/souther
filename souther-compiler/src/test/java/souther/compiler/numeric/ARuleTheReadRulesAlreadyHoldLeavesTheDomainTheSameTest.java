package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Saying a rule that the rules already read hold gives back the domain it was said to.
 *
 * <p>Only rules that have been read can show it: a domain nobody has read yet holds what was said
 * and not what that comes to, so nothing is looked for in it. What a domain was made from having
 * read counts as reading, since the rules said since are read onto those. A bound is held already
 * where a bound on the same form is as low or lower, and a looser or an equal one adds nothing; a
 * tighter one does, and so does a bound on another position.
 */
class ARuleTheReadRulesAlreadyHoldLeavesTheDomainTheSameTest {

    private static final String A = "a";
    private static final String B = "b";

    private static final Map<String, NumberSpace> DENSE = Map.of(
            A, NumberSpace.spacedOnly(Granularity.DENSE),
            B, NumberSpace.spacedOnly(Granularity.DENSE));

    private static LinearForm<String> from(String atom, long n) {
        return LinearForm.atomMinusConstant(atom, ExactRatio.of(n));
    }

    private static NumericDomain<String> top() {
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
    }

    private static NumericDomain<String> upTo(NumericDomain<String> from, String atom, long n) {
        return from.assume(from(atom, n), Rel.LE, DENSE);
    }

    @Test
    void aLooserOrAnEqualBoundIsHeldAlreadyOnceTheRulesAreRead() {
        NumericDomain<String> read = upTo(top(), A, 5);
        read.rulesRead();

        assertSame(read, upTo(read, A, 5));
        assertSame(read, upTo(read, A, 7));
    }

    @Test
    void aTighterBoundOrAnotherPositionIsNotHeld() {
        NumericDomain<String> read = upTo(top(), A, 5);
        read.rulesRead();

        assertNotSame(read, upTo(read, A, 3));
        assertNotSame(read, upTo(read, B, 9));
    }

    @Test
    void rulesNobodyHasReadAreNotLookedInto() {
        NumericDomain<String> unread = upTo(top(), A, 5);

        assertNotSame(unread, upTo(unread, A, 7));
    }

    @Test
    void whatTheDomainItWasMadeFromHadReadCountsAsRead() {
        NumericDomain<String> read = upTo(top(), A, 5);
        read.rulesRead();
        NumericDomain<String> since = upTo(read, B, 9);

        assertSame(since, upTo(since, A, 7));
        assertEquals(upTo(upTo(top(), A, 5), B, 9).rulesRead(), upTo(since, A, 7).rulesRead());
    }
}
