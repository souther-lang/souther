package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No object the state of a reading holds has a collection in it that can change, except the ones
 * said here not to.
 *
 * <p>What a reading compares, or leaves alone, is compared by what it holds or as the very object;
 * neither sees a collection inside a record that is added to. The roles say which fields are
 * compared and how, and this asks of the objects in them, for the lookups that go through the
 * readings kept, that none holds a collection which is not immutable.
 *
 * <p>Asked of these models and not of the conformance corpora: the corpora do not go through the
 * readings kept, so a population of them would audit nothing.
 */
class EveryObjectTheStateOfAReadingHoldsIsAsItWasMadeTest {

    /**
     * The collections that can change and are not changed, and why. One entry per component, with
     * what it is instead; a component added is a question — is this changed after it is made, and
     * does a reading that compares it see so.
     */
    private static final Map<String, String> NOT_CHANGED = Map.of(
            "souther.compiler.core.Core$Call.args",
            "the program: a node of the core is made once and read by every phase after",
            "souther.compiler.core.Core$Construct.values",
            "the program: a node of the core is made once and read by every phase after",
            "souther.compiler.core.Core$ListLit.elements",
            "the program: a node of the core is made once and read by every phase after",
            "souther.compiler.numeric.LinearForm.coefs",
            "an ordered map of this compiler's, which has no way to put or remove",
            "souther.compiler.inputs.TermPath.steps",
            "the steps of a path, an immutable list that works its hash out once");

    @Test
    void theObjectsTheLookupsHoldAreNotChangedInPlace() {
        ReadingState.FOUND.clear();
        ReadingState.auditing = true;
        try {
            TheLookupOfAFilteredAverageIsReadInATableOfAnyLengthTest.unread(3,
                    TheLookupOfAFilteredAverageIsReadInATableOfAnyLengthTest.ABOVE_THE_BOUND);
        } finally {
            ReadingState.auditing = false;
        }

        Map<String, String> unsaid = new TreeMap<>();
        for (String found : ReadingState.FOUND) {
            String component = found.substring(0, found.indexOf(" is a "));
            if (!NOT_CHANGED.containsKey(component)) {
                unsaid.put(component, found);
            }
        }
        assertEquals(Map.of(), unsaid, "a collection that can change in an object a reading holds");
    }

    @Test
    void aRecordHoldingAListThatCanBeAddedToIsFound() {
        record AHolder(List<String> held) {}
        ReadingState.FOUND.clear();
        ReadingState.auditing = true;
        try {
            class AnOwner {
                final List<AHolder> holders = new ArrayList<>();
            }
            ReadingState reading = new ReadingState(AnOwner.class,
                    Map.of("holders", ReadingRole.INPUT));
            AnOwner owner = new AnOwner();
            owner.holders.add(new AHolder(new ArrayList<>()));
            reading.inputsOf(owner);
        } finally {
            ReadingState.auditing = false;
        }

        assertTrue(ReadingState.FOUND.stream().anyMatch(one -> one.contains("AHolder.held")),
                ReadingState.FOUND.toString());
    }
}
