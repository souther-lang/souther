package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison on a clamped quantity draws its line in the case of the clamp where it does not
 * clamp, and the classes that line cuts run over the whole of the quantity.
 *
 * <p>{@code List.length(List.drop(1, xs)) >= 1} turns at {@code List.length(xs) == 2}, and the
 * line is read in the case {@code List.length(xs) >= 1}. The class below the line, {@code xs == []},
 * lies wholly outside that case and is still a place the comparison is reached with a value: it is
 * owed a row, and it is not a place no value stands.
 */
class APointBelowTheCaseAClampedComparisonIsReadInIsStillOwedARowTest {

    private static String modelComparing(String condition) {
        return """
                module p
                data Yes
                data No
                behavior f : (xs: List<Int>) -> Yes | No
                let f (xs) = if CONDITION then Yes else No
                """.replace("CONDITION", condition);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theOutPointOfALengthAfterADropIsNotOneNoValueStandsAt() {
        String human = report(modelComparing("List.length(List.drop(1, xs)) >= 1"));

        assertFalse(human.contains("no row can stand at the OUT point"), human);
    }

    @Test
    void theSameComparisonAsStrictlyMoreThanNoughtIsNotRefutedEither() {
        String human = report(modelComparing("List.length(List.drop(1, xs)) > 0"));

        assertFalse(human.contains("no row can stand at the OUT point"), human);
    }

    @Test
    void theSameComparisonAsNotEmptyIsNotRefutedEither() {
        String human = report(modelComparing("Bool.not(List.isEmpty(List.drop(1, xs)))"));

        assertFalse(human.contains("no row can stand at the OUT point"), human);
    }

    @Test
    void aRowCanBeWrittenAtThePoint() {
        String human = report(modelComparing("List.length(List.drop(1, xs)) >= 1"));

        assertFalse(human.contains("nothing could show a row can be written at the OUT point"),
                human);
    }

    /** A declaration that leaves no empty list is a reason the rules give, and it still refutes. */
    @Test
    void aPointTheDeclarationsLeaveNoValueAtIsStillRefuted() {
        String human = report("""
                module p
                data Yes
                data No
                data Xs = { items: List<Int> }
                    invariant nonEmpty = List.length(items) >= 1
                behavior f : (xs: Xs) -> Yes | No
                let f (xs) = if List.length(List.drop(1, xs.items)) >= 1 then Yes else No
                """);

        assertTrue(human.contains("no OUT point is owed at List.length(xs.items) = 2"), human);
    }

    /** A guard that turns an empty list back before the comparison leaves the point unreachable. */
    @Test
    void aPointAGuardBeforeTheComparisonTurnsBackIsStillRefuted() {
        String human = report("""
                module p
                data Yes
                data No
                behavior f : (xs: List<Int>) -> Yes | No
                let f (xs) =
                    if List.length(xs) >= 1
                    then if List.length(List.drop(1, xs)) >= 1 then Yes else No
                    else No
                """);

        assertTrue(human.contains("no OUT point is owed at List.length(xs) = 2"), human);
    }
}
