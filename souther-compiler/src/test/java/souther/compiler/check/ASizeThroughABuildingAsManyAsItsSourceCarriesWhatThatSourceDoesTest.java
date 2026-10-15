package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * A size of what an operation builds as many as its source is the size of that source, and carries
 * what that source's size carries however the source is reached.
 *
 * <p>Held where a name stands between them: {@code xs} below is a name for a list built by dropping
 * from another, which says it holds no more than that one. Its size and the size of its reversal
 * are one atom, and the two namings of it have to carry one thing — read through the reversal and
 * stopped at the name, the atom would carry less than it does read straight through the name, and
 * the check refuses an atom with two answers.
 */
class ASizeThroughABuildingAsManyAsItsSourceCarriesWhatThatSourceDoesTest {

    @Test
    void aReversalOfANameIsAsLongAsWhatTheNameWasGiven() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In = { k: Int }
                data Out = { holds: Bool }

                behavior same : (i: In) -> Out constructs Out
                let same (i) = Out { holds = {
                        let xs = List.drop(i.k, [0, 1])
                        List.length(List.reverse(xs)) == List.length(xs)
                    } }
                """));
    }
}
