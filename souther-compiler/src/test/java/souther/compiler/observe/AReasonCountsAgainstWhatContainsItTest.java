package souther.compiler.observe;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which behaviors a reason is a reason about.
 *
 * <p>A report marks a behavior partial where a reason counts against it, so this decides whose
 * numbers stop being answers. The question each scope answers is the same one — is this behavior
 * inside what the subject names — and only the way to answer it differs.
 *
 * <p>{@code POSITION} is the scope that has never been asked. Nothing writes one into the list a
 * report reads, so the branch that would answer for it has only ever been reached by the scopes
 * that name something a behavior sits in. A position sits inside <em>one</em> behavior, and
 * answering true for the rest of the module marks behaviors partial over a value read at a position
 * that is not theirs.
 */
class AReasonCountsAgainstWhatContainsItTest {

    @Test
    void aBehaviorScopedReasonCountsAgainstThatBehaviorAlone() {
        Incompleteness gap = Incompleteness.of(Incompleteness.Code.ROW_UNDECIDED,
                Incompleteness.Scope.BEHAVIOR, "submit");

        assertTrue(gap.countsAgainst("submit"));
        assertFalse(gap.countsAgainst("cancel"));
    }

    /** A module holds every behavior in it, by what a module is. */
    @Test
    void aModuleReasonCountsAgainstEveryBehaviorInIt() {
        Incompleteness module = Incompleteness.of(Incompleteness.Code.INSTRUMENTATION_ABSENT,
                Incompleteness.Scope.MODULE, "example.trip");

        assertTrue(module.countsAgainst("submit"));
        assertTrue(module.countsAgainst("cancel"));
    }

    /**
     * A source counts against every behavior because of what is written there, not because a source
     * is larger than a behavior.
     *
     * <p>Both places that write a {@code SOURCE} write it for a source that was not evaluated at
     * all, and which behaviors wrote rows in it is exactly what could not be read. So every one of
     * them is missing rows the source may have held. A source whose contents were known would need
     * the compilation to say which behaviors those were, and nothing writes one — this is the claim
     * to read again if something does.
     */
    @Test
    void aSourceThatWasNotEvaluatedCountsAgainstEveryBehavior() {
        Incompleteness source = Incompleteness.of(Incompleteness.Code.OBSERVATION_ABSENT,
                Incompleteness.Scope.SOURCE, "trip.sou");

        assertTrue(source.countsAgainst("submit"));
        assertTrue(source.countsAgainst("cancel"));
    }

    /**
     * And neither of them claims to know which behavior it is about.
     *
     * <p>What a target names is one thing and what holds a behavior is another. A source id is a
     * file; it does not carry which behaviors wrote rows in it, so nothing on the target answers
     * that and the reading above is stated where it is made.
     */
    @Test
    void nothingLargerThanABehaviorNamesOne() {
        assertEquals(java.util.Optional.empty(),
                Incompleteness.of(Incompleteness.Code.OBSERVATION_ABSENT,
                        Incompleteness.Scope.SOURCE, "trip.sou").behavior());
        assertEquals(java.util.Optional.empty(),
                Incompleteness.of(Incompleteness.Code.INSTRUMENTATION_ABSENT,
                        Incompleteness.Scope.MODULE, "example.trip").behavior());
    }

    /** A position is inside one behavior, and it says which one it is. */
    @Test
    void aPositionScopedReasonCountsAgainstTheBehaviorItIsIn() {
        Incompleteness gap = Incompleteness.atPosition(Incompleteness.Code.VALUE_TRUNCATED,
                "submit", "request.kind");

        assertEquals(Incompleteness.Scope.POSITION, gap.scope());
        assertEquals("submit/request.kind", gap.subject());
        assertTrue(gap.countsAgainst("submit"));
        assertFalse(gap.countsAgainst("cancel"),
                "a position of `submit` is not a reason about `cancel`");
    }

    /**
     * And there is no way to make one without saying which behavior it is in.
     *
     * <p>The subject reads as a name and is two, so a producer that had only the name would have to
     * spell the pair and a reader would have to take it apart again. That is the distinction going
     * back into a string, which is what left the position unanswerable in the first place.
     */
    @Test
    void aPositionCannotBeMadeFromASubjectAlone() {
        assertThrows(IllegalArgumentException.class,
                () -> Incompleteness.of(Incompleteness.Code.VALUE_TRUNCATED,
                        Incompleteness.Scope.POSITION, "submit/request.kind"));
    }
}
