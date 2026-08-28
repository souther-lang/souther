package souther.compiler.query;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An account of one behavior's points searches that behavior's lines and no other's.
 *
 * <p>A search costs a decoder run at every point it settles, so an account gathered from a map over
 * the module pays for every behavior in it whichever one it was asked about. What it walks is
 * {@link GenerationScope}'s to say, and a scope that is stated and then not walked is the one
 * mistake a scope cannot report: the answers come back right and the work is done anyway.
 *
 * <p>Read off what was asked rather than off how long it took. A search is kept once made, so a walk
 * that searched another behavior in passing costs nothing the second time and shows up in no clock.
 */
class AskingOneBehaviorForRowsSearchesNoOtherTest {

    /** Two behaviors, each with a guard of its own, so each has lines nothing else reads. */
    private static final String TWO = """
            module example.apart

            data Ok
            data No

            behavior first : (n: Int) -> Ok | No
            let first (n) = {
                guard n > 10 else No
                Ok
            }

            behavior second : (m: Int) -> Ok | No
            let second (m) = {
                guard m > 20 else No
                Ok
            }
            """;

    @Test
    void theOtherBehaviorsLinesAreNotSearched() {
        // Asked and nothing else. A compilation told to answer everything has searched every
        // behavior before this can look, which is the one arrangement that cannot see the
        // difference.
        Compilation compilation = Compilation.ofSource(TWO, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Db db = compilation.db();

        BorderAccount account = Adequacy.accountFor(db, "example.apart",
                new GenerationScope.Behavior("first"));
        assertNotNull(account, "the model under test compiles");

        assertTrue(db.isComputed(new Adequacy.BoundarySearch("example.apart", "first")),
                "the behavior this was asked about was searched");
        assertFalse(db.isComputed(new Adequacy.BoundarySearch("example.apart", "second")),
                "and the one it was not asked about was not");
    }
}
