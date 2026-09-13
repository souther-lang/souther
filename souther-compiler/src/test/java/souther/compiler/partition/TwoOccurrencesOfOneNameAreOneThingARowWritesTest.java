package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.types.FixtureReferenceOrigin;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A composed reference is numbered to tell one occurrence from another, and what a row writes is
 * not.
 *
 * <p>Both halves are relied on, and by different readers. A run that composes the same name twice
 * has composed two references and says so, which is what the numbering is for. A reader asking
 * whether two values are one thing to write — whether one {@code with} answers every asking a row
 * makes, or whether two rows are one piece of work — is asking about the line, and two occurrences
 * of one name are one line.
 *
 * <p>Held here because the second half is what a reader keys on, and the first half is what it would
 * be keying on if it compared the values as they are made. Nothing stops a value from being a name:
 * a row offered for a position names what the module already states.
 */
class TwoOccurrencesOfOneNameAreOneThingARowWritesTest {

    private static final String MODULE = "example.named";

    private static final String NAME = "standard";

    @Test
    void twoReferencesToOneNameAreTwoValuesAndOneLine() {
        FixtureTemplate first = FixtureTemplate.named(MODULE, NAME, new FixtureReferenceOrigin(0));
        FixtureTemplate second = FixtureTemplate.named(MODULE, NAME, new FixtureReferenceOrigin(1));

        assertNotEquals(first, second,
                "a run that composed the name twice composed two references");
        assertEquals(first.text(), second.text(),
                "and a row writes the same line for either of them");
    }
}
