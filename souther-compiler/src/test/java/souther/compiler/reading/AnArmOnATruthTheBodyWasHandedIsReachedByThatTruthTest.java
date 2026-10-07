package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ArmProbe;
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
        for (String spelled : List.of("open == true", "true == open", "open /= false")) {
            assertEquals(bare, shapesOf(spelled),
                    () -> "`" + spelled + "` reaches the arms as `open` does: "
                            + armsOf(spelled).values());
        }
    }

    /** The shape of the one way into each arm, in an order that does not turn on the plan's. */
    private static List<List<String>> shapesOf(String condition) {
        List<List<String>> out = new ArrayList<>();
        for (PathAccess each : armsOf(condition).values()) {
            assertInstanceOf(PathAccess.Ways.class, each,
                    () -> "every arm under `" + condition + "` is reached: " + each);
            out.add(shapes((PathAccess.Ways) each));
        }
        out.sort(Comparator.comparing(List::toString));
        return out;
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
