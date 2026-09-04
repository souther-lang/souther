package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module that spreads a declaration whose rules could not be worked out emits nothing.
 *
 * <p>A boundary is what a value is held to, so a decoder is built from every rule about the value or
 * from none of them: what it does not enforce is what crosses, and a value the model refuses would
 * arrive as one the model admits with nothing saying a rule went unread. A reading may go on with
 * part of the rules and say what it did not get; a decoder may not.
 *
 * <p><b>What holds this, measured.</b> Not the refusal in {@code CodecGen}. The module here gets as
 * far as being lowered and prepared and then stops, because an input the emission takes is itself
 * short where the spread reaches a module nothing expanded — replace the refusal with the clauses it
 * did reach and this still passes. So what is pinned is the outcome and not the mechanism, and the
 * refusal beside it is a guard on a state no source reaches today rather than the thing keeping this
 * green. Said here because a reader who took the two for one would delete the wrong one.
 *
 * <p>The rule is another module's on purpose. A cycle in the emitting module is stopped by that
 * module's own precondition and would say nothing about a rule reached through a spread.
 */
class ADecoderIsNotBuiltFromTheRulesThatHappenedToBeReadableTest {

    /** The module whose values are not well founded, so nothing expands its clauses. */
    private static final String OWNER = """
            module owner exposing ( Held )

            let floor = floor

            data Held = { n: Int }
                invariant n >= floor
            """;

    /** Its neighbour, which spreads that declaration and is otherwise fine. */
    private static final String SPREADS = """
            module app.rows exposing ( Row )

            import owner ( Held )

            data Row = { ...Held, m: Int }
            """;

    /** The same pair with the cycle gone, which is what says the refusal is about the cycle. */
    private static final String WELL_FOUNDED = OWNER.replace("let floor = floor", "let floor = 1");

    private static Map<String, ClassFileImage> classesOf(String owner) {
        Compilation compilation =
                Compilation.ofSources(List.of(owner, SPREADS), ModulePath.EMPTY);
        compilation.answerEverything();
        return compilation.db().ask(new Output.Classes("app.rows")).present()
                ? compilation.db().ask(new Output.Classes("app.rows")).value() : Map.of();
    }

    /**
     * The module that spreads the unreadable rule emits nothing, and the same module emits its class
     * once the rule can be read.
     *
     * <p>Both halves in one test: a refusal that also refuses the well founded model refuses
     * everything, and would pass an assertion about the first alone.
     */
    @Test
    void aRuleThatCouldNotBeReadStopsTheClassesComingOut() {
        assertTrue(classesOf(OWNER).isEmpty(),
                "a decoder built from the rules that were readable would hold a value to less than"
                        + " the model states, so the classes do not come out");
        assertFalse(classesOf(WELL_FOUNDED).isEmpty(),
                "and the same module emits once the rule it spreads can be read");
    }
}
