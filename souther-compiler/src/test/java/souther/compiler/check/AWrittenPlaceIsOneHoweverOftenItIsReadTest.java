package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.values.AuthoredOccurrence;

import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A written place is one place however often it is read, and two places written the same way are
 * two.
 *
 * <p>What the occurrences are for is that a machine refused far from any clause can name what asked
 * for it. Made afresh at each visit, the token would say which reading looked rather than what
 * somebody wrote — a clause is read once for its declaration and again for its rule, and the two
 * would be two places nobody wrote. Held by what a node is equal to instead, two conjuncts written
 * alike would be one place, and a refusal at either would be reported at both.
 *
 * <p>So it is the node itself, which is the rule the parts of a reading are already filed under.
 * This is that rule made checkable where the token is handed out.
 */
class AWrittenPlaceIsOneHoweverOftenItIsReadTest {

    private static final SourcePos AT = new SourcePos(1, 1);

    /** Two readings of one node, which is one written place. */
    @Test
    void oneNodeReadTwiceIsOnePlace() {
        AuthoredOccurrences occurrences = new AuthoredOccurrences();
        Core once = new Core.Bool(true, Type.BOOL, AT);

        assertSame(occurrences.of(once), occurrences.of(once),
                "a clause is read for its declaration and again for its rule, and what somebody"
                        + " wrote did not become two things in between");
    }

    /** And two nodes written the same way, which are two written places. */
    @Test
    void twoNodesWrittenAlikeAreTwoPlaces() {
        AuthoredOccurrences occurrences = new AuthoredOccurrences();
        Core one = new Core.Bool(true, Type.BOOL, AT);
        Core other = new Core.Bool(true, Type.BOOL, AT);

        assertNotSame(occurrences.of(one), occurrences.of(other),
                "two conjuncts written the same way are two places in a clause, and a refusal at"
                        + " one of them is not a refusal at the other");
    }

    /** And an occurrence is told from another by being it, and by nothing it holds. */
    @Test
    void anOccurrenceIsToldFromAnotherByBeingIt() {
        assertNotSame(AuthoredOccurrence.another(), AuthoredOccurrence.another());
    }
}
