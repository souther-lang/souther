package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.flow.Ways;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a guard's block goes on holds the ways past the guard as the reading answered them: every
 * way written down, or that the reading cannot enumerate them.
 *
 * <p>Two answers a list cannot tell apart. Held as a list, a guard whose ways this reading could not
 * write down came out as the same empty list as a guard no way goes past, and the first is this
 * compiler falling short while the second is what the model settles.
 */
class TheRestOfTheBlockKeepsWhatTheReadingSaidOfTheWaysTest {

    private static final String MODEL = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, amount: Int, open: Bool) -> Done | Refused
                constructs Done

            let settle (kind, amount, open) = {
                guard CONDITION else Refused
                match kind with
                    | Plain -> Done { n = 1 }
                    | Express -> Done { n = 2 }
            }
            """;

    /** What the reading said of the ways past each guard of {@code settle}. */
    private static List<Ways<List<ControlClaim>>> waysPast(String condition) {
        Compilation compilation = Compilation.ofSource(MODEL.replace("CONDITION", condition),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        Map<String, CoverageRead.Read> reads =
                compilation.db().ask(new Adequacy.Meets("example.settle")).value();
        assertNotNull(reads.get("settle"), "the body is read");
        List<Ways<List<ControlClaim>>> out = new ArrayList<>();
        for (TheRestOfTheBlock each : reads.get("settle").restOfTheBlock().values()) {
            out.add(each.ways());
        }
        assertEquals(1, out.size(), () -> "one guard, so one place the block goes on: " + out);
        return out;
    }

    /** A condition whose value turns on a fork inside it is one the reading cannot enumerate the
     *  ways of, and the place the block goes on says that — not that there is no way on. */
    @Test
    void waysTheReadingCannotEnumerateAreHeldAsThat() {
        assertTrue(waysPast("(if amount > 0 then amount else 0 - amount) > 4").getFirst()
                        instanceof Ways.Unknown<List<ControlClaim>>,
                "the ways past the guard are not something the reading could write down");
    }

    /** And a condition it can is held as the ways it wrote down. */
    @Test
    void waysTheReadingEnumeratesAreHeldAsThose() {
        Ways<List<ControlClaim>> ways = waysPast("amount > 0").getFirst();
        assertTrue(ways instanceof Ways.Known<List<ControlClaim>>(
                        List<List<ControlClaim>> paths) && paths.size() == 1,
                () -> "one way past the guard, written down: " + ways);
        assertEquals(List.of(false), placesOf(ways).stream()
                        .map(at -> at instanceof ControlPlace.Arm).toList(),
                () -> "and it is the comparison, with nothing of the arm beside it: " + ways);
    }

    /**
     * A truth the body was handed comes out a way at no comparison, and the way past a guard on
     * one is the run going down the arm that goes on.
     */
    @Test
    void theWayPastAGuardOnATruthIsTheArmThatGoesOn() {
        Ways<List<ControlClaim>> ways = waysPast("open").getFirst();
        assertEquals(List.of(true), placesOf(ways).stream()
                        .map(at -> at instanceof ControlPlace.Arm).toList(),
                () -> "one way past the guard, seen at the arm: " + ways);
    }

    /**
     * And beside a comparison, the comparison and the arm: the arm says what the comparison does
     * not, and the comparison is still what a row is steered by.
     */
    @Test
    void theWayPastAGuardOnATruthAndAComparisonIsBoth() {
        Ways<List<ControlClaim>> ways = waysPast("amount > 0 && open").getFirst();
        assertEquals(List.of(false, true), placesOf(ways).stream()
                        .map(at -> at instanceof ControlPlace.Arm).toList(),
                () -> "one way past the guard, the comparison and the arm: " + ways);
    }

    /** Where each claim of the one way written down is made. */
    private static List<ControlPlace> placesOf(Ways<List<ControlClaim>> ways) {
        if (!(ways instanceof Ways.Known<List<ControlClaim>>(List<List<ControlClaim>> paths))
                || paths.size() != 1) {
            throw new AssertionError("one way past the guard, written down: " + ways);
        }
        return paths.getFirst().stream().map(ControlClaim::at).toList();
    }
}
