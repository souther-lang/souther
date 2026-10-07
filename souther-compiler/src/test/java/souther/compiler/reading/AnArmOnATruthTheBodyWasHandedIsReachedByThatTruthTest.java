package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.types.WrittenOwner;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An arm of a fork on a truth the body was handed is reached by that truth, said of the position
 * that holds it.
 *
 * <p>The truth comes out a way at no comparison, so the condition's ways cannot be written down
 * from what a run records of the condition. The arm can: a run down it is a run that brought the
 * truth out that way, and the position is what a row is composed at. Read without that, every arm
 * of such a fork was one no way in could be stated for, and so was everything under it.
 */
class AnArmOnATruthTheBodyWasHandedIsReachedByThatTruthTest {

    private static final String MODEL = """
            module example.settle

            data Big
            data Small
            data Shut

            behavior settle : (open: Bool, amount: Int) -> Big | Small | Shut

            let settle (open, amount) =
                if CONDITION then (if amount > 10 then Big else Small) else Shut
            """;

    @Test
    void eachArmIsReachedByTheTruthAndWhatIsUnderIt() {
        assertEquals(List.of(
                        List.of("Case(open=false)"),
                        List.of("Case(open=true)", "Side"),
                        List.of("Case(open=true)", "Side"),
                        List.of("Case(open=true)")),
                shapesOf("open"),
                () -> "the arms of the fork on the truth hold it one way each, and the arms under"
                        + " it hold it beside their comparison: " + armsOf("open").values());
    }

    /**
     * The truth written against a value the source settles is the same truth, and its arms are
     * reached by it the same way.
     *
     * <p>Held to the reading of the bare position rather than to a list of its own, so that what
     * is compared is the one thing that may differ.
     */
    @Test
    void theTruthWrittenAgainstASettledValueReachesTheArmsTheSameWay() {
        List<List<String>> bare = shapesOf("open");
        for (String spelled : List.of("open == true", "true == open", "open /= false",
                "Bool.not(open == false)")) {
            assertEquals(bare, shapesOf(spelled),
                    () -> "`" + spelled + "` reaches the arms as `open` does: "
                            + armsOf(spelled).values());
        }
    }

    /** And denied, the truth the other way round, however that is written. */
    @Test
    void theTruthDeniedReachesTheArmsAsItsOtherWayDoes() {
        List<List<String>> failing = shapesOf("open == false");
        for (String spelled : List.of("Bool.not(open)", "Bool.not(open == true)")) {
            assertEquals(failing, shapesOf(spelled),
                    () -> "`" + spelled + "` reaches the arms as `open == false` does: "
                            + armsOf(spelled).values());
        }
    }

    /**
     * Beside a comparison, the truth and the comparison: the arm a run took on both holding is
     * where the truth is seen, and the comparison is seen where it is anywhere.
     */
    @Test
    void anArmOnATruthAndAComparisonIsReachedByBoth() {
        List<List<String>> underTheTruth = new ArrayList<>();
        for (PathAccess each : armsOf("open && amount > 0").values()) {
            if (each instanceof PathAccess.Ways ways && theModels(ways)
                    && shapes(ways).contains("Case(open=true)")) {
                underTheTruth.add(shapes(ways));
            }
        }
        underTheTruth.sort(Comparator.comparing(List::toString));
        assertEquals(List.of(List.of("Side", "Case(open=true)", "Side"),
                        List.of("Side", "Case(open=true)", "Side"),
                        List.of("Side", "Case(open=true)")),
                underTheTruth, () -> "the arm the fork takes on both holding, and the arms under"
                        + " it, hold the truth and the comparisons: "
                        + armsOf("open && amount > 0").values());
    }

    /**
     * The shape of the one way into each of the model's own arms, in an order that does not turn
     * on the plan's. An operation of the language's own written as a body has arms of its own,
     * which are where it stands and not the model's.
     */
    private static List<List<String>> shapesOf(String condition) {
        List<List<String>> out = new ArrayList<>();
        for (PathAccess each : armsOf(condition).values()) {
            if (each instanceof PathAccess.Ways ways && !theModels(ways)) {
                continue;
            }
            assertInstanceOf(PathAccess.Ways.class, each,
                    () -> "every arm under `" + condition + "` is reached: " + each);
            out.add(shapes((PathAccess.Ways) each));
        }
        out.sort(Comparator.comparing(List::toString));
        return out;
    }

    /** Whether the arm {@code ways} arrives at is one the model wrote. */
    private static boolean theModels(PathAccess.Ways ways) {
        return ways.arrivesAt().at() instanceof ControlPlace.Arm arm
                && arm.arm().origin().owner() instanceof WrittenOwner.Body(var module, var _)
                && module.equals("example.settle");
    }

    /** What each condition of the one way in is, with the truth a case holds written out. */
    private static List<String> shapes(PathAccess.Ways ways) {
        assertEquals(1, ways.ways().size(), () -> "one way in: " + ways);
        return ways.ways().getFirst().conditions().stream()
                .map(each -> each instanceof Condition.Case(var at, var names)
                        ? "Case(" + at + "=" + String.join("|", names) + ")"
                        : each.getClass().getSimpleName())
                .toList();
    }

    private static Map<ArmProbe, PathAccess> armsOf(String condition) {
        Compilation compilation = Compilation.ofSource(MODEL.replace("CONDITION", condition),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        CoverageRead.Read read =
                compilation.db().ask(new Adequacy.Meets("example.settle")).value().get("settle");
        assertNotNull(read, "the body is read");
        return read.arms();
    }
}
