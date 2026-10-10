package souther.compiler.proof;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element of a list of pairs is read, where a law asks what it is filed under, as filed under
 * the first of the pair — what a map made of the list files the second under.
 *
 * <p>Asked of how many different keys a written list of two pairs comes to. The two pairs share
 * their first and differ in their second, so the second pair is no new key, and that is decided
 * by the pairs themselves. Read as filed under a key nothing ties to the pair, whether the second
 * key is new is a question left open.
 */
class AnElementOfAListOfPairsIsFiledUnderItsFirstTest {

    @Test
    void twoPairsSharingTheirFirstComeToOneKey() {
        Value key = new Value.Fresh(1, "a key");
        Value first = new Value.Tupled(List.of(key, new Value.Fresh(2, "one value")));
        Value second = new Value.Tupled(List.of(key, new Value.Fresh(3, "another value")));
        Reading reading = new Reading(null, Set.of());

        LinearForm<LawNumber<Value>> keys = reading.different(
                new Value.Listed(List.of(first, second)), Reading.Element::key);

        // The first pair is a new key whatever it is, and the second is one only where its key is
        // not the first's, which it is.
        assertTrue(keys.coefs().containsKey(new LawNumber.HowManyMeet<>(
                        new Value.Listed(List.of(second)), new LawProposition.Always<>(false))),
                () -> "the second pair is counted as a key unless it is the first's: " + keys);
    }
}
